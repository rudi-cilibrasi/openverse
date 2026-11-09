#!/usr/bin/env bash
# Everything that needs no QuickProof: the Lean proofs and front end, the C runtime and its tests,
# both implementations on the Verse test suite, differential fuzzing, and the QuickProof pins.
#
# After the build and the C runtime, the remaining checks are independent of each other: they run
# concurrently, at most CHECK_JOBS at a time (default: the number of CPUs), longest first so they
# pack well, and each one's output is printed, in this order, once it has finished. CHECK_JOBS=1
# runs them one after another.
#
# Every fuzzer starts at seed FUZZ_SEED (default 1), and its count comes from its own variable
# (FUZZ_MODEL_MV=1400, …): the nightly workflow (.github/workflows/fuzz-nightly.yml) runs ten times
# the counts from a seed that changes each day, and `FUZZ_SEED=N scripts/check.sh` reproduces it.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
echo "== lake build (Lean proofs, front end, reference interpreter)"
lake build 2>&1 | tail -1
if grep -rnE '\bsorry\b|\badmit\b' OpenVerse/ Main.lean; then echo "error: sorry/admit in Lean sources" >&2; exit 1; fi
scripts/gen-claims.sh --check
echo "== C runtime"
make -s -C runtime test

seed="${FUZZ_SEED:-1}"
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
check "class-feature fuzzing (${FUZZ_CLASSES:-200} programs)" scripts/fuzz-classes.sh "${FUZZ_CLASSES:-200}" "$seed"
check "differential fuzzing (${FUZZ:-1000} random programs)" scripts/fuzz-diff.sh "${FUZZ:-1000}" "$seed"
check "Verse test suite, Lean and C" scripts/test-verse.sh --c
check "front-end mutation fuzzing (${FUZZ_FRONT:-500} mutants)" scripts/fuzz-front.sh "${FUZZ_FRONT:-500}" "$seed"
check "QuickProof pins" scripts/check-quickproof-pins.sh
check "float fuzzing (${FUZZ_FLOATS:-200} programs, against Python's doubles)" scripts/fuzz-floats.sh "${FUZZ_FLOATS:-200}" "$seed"
check "choice fuzzing (${FUZZ_CHOICE:-200} programs, against a backtracking model)" scripts/fuzz-choice.sh "${FUZZ_CHOICE:-200}" "$seed"
check "scheduler model fuzzing (${FUZZ_MODEL_SCHED:-50} programs, against a model of the docs)" \
  scripts/fuzz-model-sched.sh "${FUZZ_MODEL_SCHED:-50}" "$seed"
check "GADT model fuzzing (${FUZZ_MODEL_GADT:-150} programs, against five models of the docs)" \
  scripts/fuzz-model-gadt.sh "${FUZZ_MODEL_GADT:-150}" "$seed"
check "choice model fuzzing (${FUZZ_MODEL_MV:-140} programs, functions with several values too)" \
  scripts/fuzz-model-mv.sh "${FUZZ_MODEL_MV:-140}" "$seed"
check "concurrency fuzzing (${FUZZ_CONC:-160} programs)" scripts/fuzz-conc.sh "${FUZZ_CONC:-160}" "$seed"
check "polymorphic-recursion concurrency fuzzing (${FUZZ_CONC_POLY:-60} programs, #244)" \
  scripts/fuzz-conc-poly.sh "${FUZZ_CONC_POLY:-60}" "$seed"
check "heap-reclamation fuzzing (${FUZZ_FIELDS:-60} programs with array fields)" scripts/fuzz-fields.sh "${FUZZ_FIELDS:-60}" "$seed"

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
