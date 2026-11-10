#!/usr/bin/env bash
# Check the runner's diagnostics and failure propagation without real builds.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
fixture="$tmp/repo with spaces"
mkdir -p "$fixture"/{bin,scripts,tests/scripts,OpenVerse} "$tmp/scratch"
cp "$root/scripts/check.sh" "$fixture/scripts/"
touch "$fixture/Main.lean"
export CHECK_TEST_EVENTS="$tmp/events"

cat >"$fixture/bin/lake" <<'SH'
#!/usr/bin/env bash
touch "$CHECK_TEST_EVENTS/lake"
echo 'build progress that should be quiet on success'
if [[ $CHECK_TEST_BUILD == fail ]]; then
  echo 'OpenVerse/Front/Elab.lean:42: type mismatch' >&2
  echo 'error: build failed'
  exit 7
fi
echo 'Build completed successfully.'
SH
cat >"$fixture/bin/make" <<'SH'
#!/usr/bin/env bash
touch "$CHECK_TEST_EVENTS/make"
SH
cat >"$tmp/check-step" <<'SH'
#!/usr/bin/env bash
name=${0##*/}
touch "$CHECK_TEST_EVENTS/$name"
if [[ $name == "$CHECK_TEST_FAIL_STEP" ]]; then
  echo 'fixture check failure detail'
  exit 3
fi
SH
chmod +x "$fixture/bin/lake" "$fixture/bin/make" "$tmp/check-step"
for script in "$root"/scripts/fuzz-*.sh "$root/scripts/test-verse.sh" \
    "$root/scripts/check-quickproof-pins.sh" "$root/scripts/gen-claims.sh"; do
  cp "$tmp/check-step" "$fixture/scripts/${script##*/}"
done
# Stubbing these also prevents the runner's own unit check from recursing.
for script in "$root"/tests/scripts/*.sh; do cp "$tmp/check-step" "$fixture/tests/scripts/${script##*/}"; done

die() { echo "test-check: $*" >&2; cat "$tmp/log" >&2; exit 1; }
run_check() {
  local jobs=$1 build=$2 expected=$3 step=${4:-} rc
  rm -rf "$CHECK_TEST_EVENTS"; mkdir "$CHECK_TEST_EVENTS"
  if PATH="$fixture/bin:$PATH" TMPDIR="$tmp/scratch" CHECK_MEM_GB=1 \
      CHECK_JOBS="$jobs" CHECK_TEST_BUILD="$build" CHECK_TEST_FAIL_STEP="$step" \
      timeout 10 bash "$fixture/scripts/check.sh" >"$tmp/log" 2>&1; then rc=0; else rc=$?; fi
  [[ $rc == "$expected" ]] || die "jobs=$jobs build=$build step=$step returned $rc, wanted $expected"
  if compgen -G "$tmp/scratch/*" >/dev/null; then die 'temporary logs were not cleaned'; fi
}

run_check 2 fail 7
grep -qF 'OpenVerse/Front/Elab.lean:42: type mismatch' "$tmp/log" || die 'build diagnostic was hidden'
[[ -f "$CHECK_TEST_EVENTS/lake" && ! -f "$CHECK_TEST_EVENTS/make" ]] || die 'continued after failed build'
for jobs in 1 2 08; do
  run_check "$jobs" success 0
  grep -q '^Build completed successfully\.$' "$tmp/log" || die 'missing build summary'
  if grep -q 'build progress' "$tmp/log"; then die 'successful build was not compact'; fi
  grep -q '^check.sh: all checks passed$' "$tmp/log" || die 'missing check summary'
  [[ -f "$CHECK_TEST_EVENTS/fuzz-fields.sh" ]] || die 'last check did not run'
done
run_check 2 success 1 fuzz-classes.sh
grep -q 'fixture check failure detail' "$tmp/log" || die 'check diagnostic was hidden'
grep -qF 'check.sh: FAILED: class-feature fuzzing' "$tmp/log" || die 'failed check was not reported'
[[ -f "$CHECK_TEST_EVENTS/fuzz-fields.sh" ]] || die 'a failed check stopped the remaining checks'
for jobs in 0 -1 invalid 9223372036854775808 18446744073709551617; do
  run_check "$jobs" success 1
  grep -q 'CHECK_JOBS must be a positive integer' "$tmp/log" || die 'missing concurrency diagnostic'
  if compgen -G "$CHECK_TEST_EVENTS/*" >/dev/null; then die 'invalid concurrency started work'; fi
done
echo 'test-check: all checks passed'
