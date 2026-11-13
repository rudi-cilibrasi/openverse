#!/usr/bin/env bash
# Run every tests/verse/*.verse with the Lean reference interpreter and compare
# stdout plus the exit code with NAME.expected. With --c, also compile each to
# OVBC and run it with the C runtime (runtime/build/cverse), which must agree
# byte for byte with the Lean result. The compiler's warnings (the lines
# `FILE:LINE:COL: warning: ...` it prints before the program runs) are compared
# with NAME.warnings, each without `FILE:`, and a program without that file
# must have none; the rest of standard error is the run's, which C must match.
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ov="$root/.lake/build/bin/openverse"
cv="$root/runtime/build/cverse"
withc=0; [[ "${1:-}" == "--c" ]] && withc=1
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
pass=0; fail=0
# the programs: the files, and the directories with a Self.verse (#27)
progs=("$root"/tests/verse/*.verse)
for d in "$root"/tests/verse/*/; do [[ -f "$d/Self.verse" ]] && progs+=("${d%/}"); done
for f in "${progs[@]}"; do
  n="$(basename "$f" .verse)"
  # NAME.args: command-line arguments, one per line (Args, `do EXPR`)
  extra=(); [[ -f "$root/tests/verse/$n.args" ]] && mapfile -t extra <"$root/tests/verse/$n.args"
  # with --c, the same compilation also writes the bytecode for cverse
  emit=(); [[ $withc -eq 1 ]] && emit=(--emit "$tmp/$n.vbc")
  { "$ov" run "$f" "${emit[@]}" "${extra[@]}" 2>"$tmp/$n.all.err"; echo "exit=$?"; } >"$tmp/$n.lean.out"
  # (the warnings, at the start of standard error, apart from the run's)
  awk -v p="$f:" -v w="$tmp/$n.lean.warn" -v e="$tmp/$n.lean.err" '
    !done && index($0, p) == 1 && index($0, ": warning: ") { print substr($0, length(p) + 1) > w; next }
    { done = 1; print > e }
    END { printf "" > w; printf "" > e }' "$tmp/$n.all.err"
  want_warn="$root/tests/verse/$n.warnings"; [[ -f "$want_warn" ]] || want_warn=/dev/null
  if ! cmp -s "$tmp/$n.lean.warn" "$want_warn"; then
    echo "FAIL $n (warnings):"; diff "$want_warn" "$tmp/$n.lean.warn" | head -10
    fail=$((fail+1)); continue
  fi
  if ! cmp -s "$tmp/$n.lean.out" "$root/tests/verse/$n.expected"; then
    echo "FAIL $n (lean):"; diff "$root/tests/verse/$n.expected" "$tmp/$n.lean.out" | head -20
    cat "$tmp/$n.lean.err" | head -5
    fail=$((fail+1)); continue
  fi
  if [[ $withc -eq 1 ]]; then
    [[ -s "$tmp/$n.vbc" ]] || { echo "FAIL $n (no bytecode)"; fail=$((fail+1)); continue; }
    { "$cv" "$tmp/$n.vbc" 2>"$tmp/$n.c.err"; echo "exit=$?"; } >"$tmp/$n.c.out"
    if ! cmp -s "$tmp/$n.lean.out" "$tmp/$n.c.out" || ! cmp -s "$tmp/$n.lean.err" "$tmp/$n.c.err"; then
      echo "FAIL $n (C differs from Lean):"; diff "$tmp/$n.lean.out" "$tmp/$n.c.out" | head -20
      diff "$tmp/$n.lean.err" "$tmp/$n.c.err" | head -5
      fail=$((fail+1)); continue
    fi
  fi
  pass=$((pass+1))
done
for f in "$root"/tests/errors/*.verse; do
  n="$(basename "$f" .verse)"
  want="$(sed -n 's/^# expect: //p' "$f" | head -1)"
  # NAME.args: options, one per line (`--signal-no-rollback`)
  extra=(); [[ -f "$root/tests/errors/$n.args" ]] && mapfile -t extra <"$root/tests/errors/$n.args"
  "$ov" check "$f" "${extra[@]}" >/dev/null 2>"$tmp/$n.err"; code=$?
  if [[ $code -ne 4 ]] || ! grep -qF "$want" "$tmp/$n.err"; then
    echo "FAIL errors/$n: exit $code, wanted 4 and '$want', got: $(cat "$tmp/$n.err")"
    fail=$((fail+1)); continue
  fi
  pass=$((pass+1))
done
echo "tests: $pass passed, $fail failed"
[[ $fail -eq 0 ]]
