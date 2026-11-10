#!/usr/bin/env bash
# Exercise fuzzers with controlled generators and runtimes.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
fixture="$tmp/repo with spaces"
mkdir -p "$fixture/scripts" "$fixture/.lake/build/bin" "$fixture/runtime/build"
cp "$root/scripts/fuzz-choice.sh" "$root/scripts/fuzz-floats.sh" "$root/scripts/fuzz-expected.sh" "$fixture/scripts/"
for kind in classes conc conc-poly fields front; do cp "$root/scripts/fuzz-$kind.sh" "$fixture/scripts/"; done
export FUZZ_TEST_CALLS="$tmp/lean.calls" FUZZ_TEST_C_CALLS="$tmp/c.calls"

cat >"$fixture/scripts/gen-choice.py" <<'PY'
import os
from pathlib import Path
import sys

seed = int(sys.argv[1])
mode = os.environ['FUZZ_TEST_MODE']
output = f'seed {seed}\n'
if len(sys.argv) == 2:
    sys.stdout.write(output)
    if seed == 2 and mode == 'generator-error':
        sys.stderr.write('injected generator error after partial output\n')
        sys.exit(9)
    sys.exit(0)
if seed == 2 and mode in ('generator-error', 'generator-silent'):
    if mode == 'generator-error':
        sys.stderr.write('injected generator error\n')
        sys.exit(9)
    sys.exit(0)
if seed != 2 or mode != 'missing-source':
    Path(sys.argv[2]).write_text(output)
if seed != 2 or mode != 'missing-expected':
    Path(sys.argv[3]).write_text('' if mode == 'empty-output' else output)
PY
cp "$fixture/scripts/gen-choice.py" "$fixture/scripts/gen-floats.py"
for kind in classes conc conc-poly fields fields2; do cp "$fixture/scripts/gen-choice.py" "$fixture/scripts/gen-$kind.py"; done
cat >"$fixture/.lake/build/bin/openverse" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'run\n' >>"$FUZZ_TEST_CALLS"
[[ $1 == run && $3 == --emit ]]
emit=1
case $FUZZ_TEST_MODE in
  no-bytecode) emit=0 ;;
  no-bytecode-second) if grep -qx 'seed 2' "$2"; then emit=0; fi ;;
esac
if (( emit )); then cp "$2" "$4"; fi
if [[ $FUZZ_TEST_MODE == lean-mismatch ]]; then echo wrong
elif [[ $FUZZ_TEST_MODE != empty-output ]]; then cat "$2"; fi
if [[ $FUZZ_TEST_MODE == lean-error ]]; then exit 2; fi
SH
cat >"$fixture/runtime/build/cverse" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'run\n' >>"$FUZZ_TEST_C_CALLS"
if [[ $FUZZ_TEST_MODE == c-mismatch ]]; then echo wrong
elif [[ $FUZZ_TEST_MODE != empty-output ]]; then cat "$1"; fi
if [[ $FUZZ_TEST_MODE == c-error ]]; then exit 2; fi
SH
chmod +x "$fixture/.lake/build/bin/openverse" "$fixture/runtime/build/cverse"

die() { echo "test-fuzz-runners: $*" >&2; cat "$tmp/log" >&2; exit 1; }
run_case() {
  local kind=$1 mode=$2 bad=$3 rc want=0
  local args=(3 1)
  if [[ $# -eq 4 ]]; then args+=("$4"); fi
  rm -f "$FUZZ_TEST_CALLS" "$FUZZ_TEST_C_CALLS" "$fixture"/fuzz-*.verse
  export FUZZ_TEST_MODE=$mode
  if bash "$fixture/scripts/fuzz-$kind.sh" "${args[@]}" >"$tmp/log" 2>&1; then rc=0; else rc=$?; fi
  if (( bad )); then want=1; fi
  [[ $rc == "$want" ]] || die "$kind/$mode returned $rc, wanted $want"
  if [[ $kind == choice || $kind == floats ]]; then
    grep -q "^fuzz-$kind: 3 programs from seed 1, $bad bad$" "$tmp/log" || die "$kind/$mode summary"
  fi
}

run_case choice success 0
run_case floats success 0
run_case choice empty-output 0
run_case floats empty-output 0
for kind in choice floats; do
  for mode in generator-error generator-silent missing-source missing-expected; do
    run_case "$kind" "$mode" 1
    grep -q 'GENERATOR FAILED seed 2' "$tmp/log" || die "$kind/$mode did not report the generator"
    [[ $(wc -l <"$FUZZ_TEST_CALLS") == 2 ]] || die "$kind/$mode ran stale input"
    [[ $(wc -l <"$FUZZ_TEST_C_CALLS") == 2 ]] || die "$kind/$mode ran stale bytecode"
  done
done
for kind in classes conc conc-poly fields; do
  run_case "$kind" generator-error 1
  grep -q 'GENERATOR FAILED seed 2' "$tmp/log" || die "$kind did not report the generator"
  [[ $(wc -l <"$FUZZ_TEST_CALLS") == 2 ]] || die "$kind ran partial input"
  [[ $(wc -l <"$FUZZ_TEST_C_CALLS") == 2 ]] || die "$kind ran partial bytecode"
done
run_case fields lean-error 0
grep -q ', 3 not runnable, 0 mismatches, 0 generator failures$' "$tmp/log" || die 'fields changed its nonrunnable policy'
[[ ! -f "$FUZZ_TEST_C_CALLS" ]] || die 'fields ran a nonrunnable program in C'
mkdir "$tmp/bin"
cat >"$tmp/bin/python3" <<'SH'
#!/usr/bin/env bash
printf 'seed 1\n' >"$4/m00000.verse"
exit 9
SH
chmod +x "$tmp/bin/python3"
PATH="$tmp/bin:$PATH" run_case front generator-error 1
grep -q 'GENERATOR FAILED seed 1' "$tmp/log" || die 'front did not report the generator'
[[ ! -f "$FUZZ_TEST_CALLS" && ! -f "$FUZZ_TEST_C_CALLS" ]] || die 'front ran an incomplete batch'
for mode in lean-mismatch lean-error no-bytecode c-mismatch c-error; do
  run_case choice "$mode" 3
  [[ $(cat "$fixture/fuzz-choice-3.verse") == 'seed 3' ]] || die "$mode did not save its input"
done
run_case choice no-bytecode-second 1
[[ $(wc -l <"$FUZZ_TEST_C_CALLS") == 2 ]] || die 'choice reused the previous bytecode'
cp "$fixture/runtime/build/cverse" "$fixture/custom-cverse"
rm "$fixture/runtime/build/cverse"
for kind in choice floats; do
  run_case "$kind" success 0 "$fixture/custom-cverse"
  FUZZ_TEST_MODE=success bash "$fixture/scripts/fuzz-$kind.sh" 1 7 "$fixture/custom-cverse" >"$tmp/log" 2>&1 || die "$kind seed selection"
  grep -q "^fuzz-$kind: 1 programs from seed 7, 0 bad$" "$tmp/log" || die "$kind ignored the first seed"
done
echo 'test-fuzz-runners: all checks passed'
