#!/usr/bin/env bash
# Everything that needs no QuickProof: the Lean proofs and front end, the C runtime and its tests,
# both implementations on the Verse test suite, differential fuzzing, and the QuickProof pins.
#
# After the build and the C runtime, the remaining checks are independent of each other: they run
# concurrently, at most CHECK_JOBS at a time (default: the number of CPUs), longest first so they
# pack well, and each one's output is printed, in this order, once it has finished. CHECK_JOBS=1
# runs them one after another.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
echo "== lake build (Lean proofs, front end, reference interpreter)"
lake build 2>&1 | tail -1
if grep -rnE '\bsorry\b|\badmit\b' OpenVerse/ Main.lean; then echo "error: sorry/admit in Lean sources" >&2; exit 1; fi
scripts/gen-claims.sh --check
echo "== C runtime"
make -s -C runtime test

logs="$(mktemp -d)"; trap 'rm -rf "$logs"' EXIT
max="${CHECK_JOBS:-$(nproc 2>/dev/null || echo 4)}"
titles=(); pids=()
# check TITLE CMD...: run CMD in the background once fewer than $max checks are running
check() {
  local i=${#titles[@]}; titles+=("$1"); shift
  while (( $(jobs -rp | wc -l) >= max )); do wait -n || true; done
  ( set +e; s=$SECONDS; "$@" >"$logs/$i" 2>&1; echo "$? $((SECONDS - s))" >"$logs/$i.rc" ) &
  pids+=($!)
}
check "class-feature fuzzing (${FUZZ_CLASSES:-200} programs)" scripts/fuzz-classes.sh "${FUZZ_CLASSES:-200}" 1
check "differential fuzzing (${FUZZ:-1000} random programs)" scripts/fuzz-diff.sh "${FUZZ:-1000}" 1
check "Verse test suite, Lean and C" scripts/test-verse.sh --c
check "front-end mutation fuzzing (${FUZZ_FRONT:-500} mutants)" scripts/fuzz-front.sh "${FUZZ_FRONT:-500}" 1
check "QuickProof pins" scripts/check-quickproof-pins.sh
check "float fuzzing (${FUZZ_FLOATS:-200} programs, against Python's doubles)" scripts/fuzz-floats.sh "${FUZZ_FLOATS:-200}" 1
check "concurrency fuzzing (${FUZZ_CONC:-100} programs)" scripts/fuzz-conc.sh "${FUZZ_CONC:-100}" 1
check "heap-reclamation fuzzing (${FUZZ_FIELDS:-60} programs with array fields)" scripts/fuzz-fields.sh "${FUZZ_FIELDS:-60}" 1

failed=()
for i in "${!titles[@]}"; do
  wait "${pids[$i]}" || true
  read -r rc secs <"$logs/$i.rc"
  echo "== ${titles[$i]} (${secs} s)"
  cat "$logs/$i"
  [[ $rc -eq 0 ]] || failed+=("${titles[$i]}")
done
if (( ${#failed[@]} )); then
  printf 'check.sh: FAILED: %s\n' "${failed[@]}" >&2
  exit 1
fi
echo "check.sh: all checks passed"
