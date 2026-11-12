#!/usr/bin/env bash
# Everything that needs no QuickProof: the Lean proofs and front end, the C runtime and its tests,
# both implementations on the Verse test suite, differential fuzzing, and the QuickProof pins.
#
# After the build, source-frame contracts and C runtime, the remaining checks are independent: they run
# concurrently, at most CHECK_JOBS at a time (default: the number of CPUs), longest first so they
# pack well, and each one's output is printed, in this order, once it has finished. CHECK_JOBS=1
# runs them one after another. CHECK_JOBS must be a positive integer.
#
# Each fuzz range starts at seed FUZZ_SEED (default 1), and its count comes from its own variable
# (FUZZ_MODEL_MV=1400, …): the nightly workflow (.github/workflows/fuzz-nightly.yml) runs ten times
# the counts from a seed that changes each day, and `FUZZ_SEED=N scripts/check.sh` reproduces it.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
max="${CHECK_JOBS:-$(nproc 2>/dev/null || echo 4)}"
# Reject counts that Bash arithmetic cannot represent exactly.
if [[ $max =~ ^0*([1-9][0-9]*)$ ]] &&
    [[ $(( BASH_REMATCH[1] )) == "${BASH_REMATCH[1]}" ]]; then
  max="${BASH_REMATCH[1]}"
else
  echo "check.sh: CHECK_JOBS must be a positive integer" >&2; exit 1
fi
logs="$(mktemp -d)"; trap 'rm -rf "$logs"' EXIT
echo "== lake build (Lean proofs, front end, reference interpreter)"
if lake build >"$logs/build" 2>&1; then
  tail -1 "$logs/build"
else
  rc=$?; cat "$logs/build"; exit "$rc"
fi
echo "== source-frame rewrite contracts"
# Like the proof build, this check loads Lean modules. Run it before the
# virtual-memory cap applied to generated programs below.
if lake env lean -j1 --run tests/lean/SourceFrameRefs.lean >"$logs/frame-contracts" 2>&1; then
  cat "$logs/frame-contracts"
else
  rc=$?; cat "$logs/frame-contracts"; exit "$rc"
fi
echo "== compiler implementation-write contracts"
if lake env lean -j1 --run tests/lean/CompilerWrites.lean >"$logs/compiler-writes" 2>&1; then
  cat "$logs/compiler-writes"
else
  rc=$?; cat "$logs/compiler-writes"; exit "$rc"
fi
echo "== failure-capture contracts"
if lake env lean -j1 --run tests/lean/FailCapture.lean >"$logs/failure-contracts" 2>&1; then
  cat "$logs/failure-contracts"
else
  rc=$?; cat "$logs/failure-contracts"; exit "$rc"
fi
echo "== suspension break contracts"
if lake env lean -j1 --run tests/lean/SuspendBreaks.lean >"$logs/break-contracts" 2>&1; then
  cat "$logs/break-contracts"
else
  rc=$?; cat "$logs/break-contracts"; exit "$rc"
fi
echo "== source-profile compiler API contracts"
if lake env lean -j1 --run tests/lean/SourceProfile.lean >"$logs/profile-contracts" 2>&1; then
  cat "$logs/profile-contracts"
else
  rc=$?; cat "$logs/profile-contracts"; exit "$rc"
fi
echo "== effect admission compiler API contracts"
if lake env lean -j1 --run tests/lean/EffectPolicy.lean >"$logs/effect-contracts" 2>&1; then
  cat "$logs/effect-contracts"
else
  rc=$?; cat "$logs/effect-contracts"; exit "$rc"
fi
echo "== concurrency-prelude compiler API contracts"
if lake env lean -j1 --run tests/lean/ConcurrencyPrelude.lean >"$logs/prelude-contracts" 2>&1; then
  cat "$logs/prelude-contracts"
else
  rc=$?; cat "$logs/prelude-contracts"; exit "$rc"
fi
if grep -rnE '\bsorry\b|\badmit\b' OpenVerse/ Main.lean; then echo "error: sorry/admit in Lean sources" >&2; exit 1; fi
scripts/gen-claims.sh --check
echo "== C runtime"
make -s -C runtime test

# (from here on, each process may use at most CHECK_MEM_GB of virtual memory, 4 by default: on
# 2026-11-09 a Lean run of a generated program reached 60 GB on a dev machine, and on a 16 GB CI
# runner one such run takes the whole job down with no message, as the nightly runs of
# 2026-11-10 were. With the cap the program fails alone, and its fuzzer saves and reports it.)
ulimit -v $(( ${CHECK_MEM_GB:-4} * 1024 * 1024 ))
seed="${FUZZ_SEED:-1}"
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
check "overloading conformance matrix" bash tests/scripts/test-overload-conformance.sh
check "effect admission and executable controls" bash tests/scripts/test-effect-admission.sh
check "construction effects and executable controls" bash tests/scripts/test-construction-effects.sh
check "scheduler conformance traces and controls" bash tests/scripts/test-scheduler-conformance.sh
check "bounded clock domain (${FUZZ_CLOCK_DOMAIN:-100} programs and boundary traces)" \
  bash tests/scripts/test-clock-domain.sh "${FUZZ_CLOCK_DOMAIN:-100}" "$seed"
check "overload domains (${FUZZ_OVERLOAD_SHAPES:-468} programs, across six contexts)" \
  bash scripts/fuzz-overload-shapes.sh "${FUZZ_OVERLOAD_SHAPES:-468}" "$seed"
check "call packing (${FUZZ_CALL_PACKING:-60} programs, across ten contexts)" \
  bash tests/scripts/test-call-packing.sh "${FUZZ_CALL_PACKING:-60}" "$seed"
check "choice-free source profile" bash tests/scripts/test-choice-profile.sh
check "small integer value sharing" bash tests/scripts/test-small-int-cache.sh
check "empty collection value sharing" bash tests/scripts/test-empty-value-cache.sh
check "front-end mutation fuzzing (${FUZZ_FRONT:-500} mutants)" scripts/fuzz-front.sh "${FUZZ_FRONT:-500}" "$seed"
check "QuickProof pins" scripts/check-quickproof-pins.sh
check "fuzz runner checks" bash tests/scripts/test-fuzz-runners.sh
check "check runner checks" bash tests/scripts/test-check.sh
check "front-end C translation-unit size" bash tests/scripts/test-frontend-c-size.sh
check "choice continuation code size" bash tests/scripts/test-choice-size.sh
check "construction/default choice models (${FUZZ_MODEL_CONSTRUCT:-60} seeds each)" \
  bash tests/scripts/test-choice-defaults.sh "${FUZZ_MODEL_CONSTRUCT:-60}" "$seed"
check "choice continuation source contexts (${FUZZ_MODEL_CONTEXTS:-60} seed pairs)" \
  bash tests/scripts/test-choice-contexts.sh "${FUZZ_MODEL_CONTEXTS:-60}" "$seed"
check "refining casts in source contexts (${FUZZ_MODEL_REFINE_CONTEXTS:-144} seed pairs)" \
  bash tests/scripts/test-refining-contexts.sh "${FUZZ_MODEL_REFINE_CONTEXTS:-144}" "$seed"
check "refining source-task cleanup (${FUZZ_MODEL_TASK_ORDER:-64} seed pairs)" \
  bash tests/scripts/test-refining-task-order.sh "${FUZZ_MODEL_TASK_ORDER:-64}" "$seed"
check "waiting consumers in parameter defaults (${FUZZ_MODEL_WAITING_DEFAULTS:-144} seed pairs)" \
  bash tests/scripts/test-waiting-defaults.sh "${FUZZ_MODEL_WAITING_DEFAULTS:-144}" "$seed"
check "float fuzzing (${FUZZ_FLOATS:-200} programs, against Python's doubles)" scripts/fuzz-floats.sh "${FUZZ_FLOATS:-200}" "$seed"
check "scalar float math (${FUZZ_FLOAT_MATH:-64} random cases and fixed edges)" \
  bash tests/scripts/test-float-math.sh "${FUZZ_FLOAT_MATH:-64}" "$seed"
check "scalar float math regression (one-ulp tiny normal, seed 23801198)" \
  bash tests/scripts/test-float-math.sh 1 23801198
check "rational arithmetic fuzzing (${FUZZ_RATIONAL:-120} programs, against exact fractions)" scripts/fuzz-rational.sh "${FUZZ_RATIONAL:-120}" "$seed"
check "choice fuzzing (${FUZZ_CHOICE:-200} programs, against a backtracking model)" scripts/fuzz-choice.sh "${FUZZ_CHOICE:-200}" "$seed"
check "scheduler model fuzzing (${FUZZ_MODEL_SCHED:-50} programs, against a model of the docs)" \
  scripts/fuzz-model-sched.sh "${FUZZ_MODEL_SCHED:-50}" "$seed"
check "GADT model fuzzing (${FUZZ_MODEL_GADT:-150} programs, against twenty-eight models of the docs)" \
  scripts/fuzz-model-gadt.sh "${FUZZ_MODEL_GADT:-150}" "$seed"
check "FIFO event model fuzzing (${FUZZ_MODEL_FIFO:-60} programs, --event-fifo)" \
  scripts/fuzz-model-fifo.sh "${FUZZ_MODEL_FIFO:-60}" "$seed"
check "heterogeneous choice model fuzzing (${FUZZ_MODEL_HETEROGENEOUS:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_HETEROGENEOUS:-120}" "$seed"
check "choice operation dictionary model fuzzing (${FUZZ_MODEL_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_DICTIONARY:-120}" "$seed" --methods
check "polymorphic choice dictionary model fuzzing (${FUZZ_MODEL_POLYMORPHIC_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_POLYMORPHIC_DICTIONARY:-120}" "$seed" --generic-methods
check "field and method choice dictionary model fuzzing (${FUZZ_MODEL_MEMBER_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_MEMBER_DICTIONARY:-120}" "$seed" --members
check "callable field choice dictionary model fuzzing (${FUZZ_MODEL_CALLABLE_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_CALLABLE_DICTIONARY:-120}" "$seed" --callable-fields
check "alias choice dictionary model fuzzing (${FUZZ_MODEL_ALIAS_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_ALIAS_DICTIONARY:-120}" "$seed" --aliases
check "field write choice dictionary model fuzzing (${FUZZ_MODEL_WRITE_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_WRITE_DICTIONARY:-120}" "$seed" --writes
check "nested field write choice dictionary model fuzzing (${FUZZ_MODEL_NESTED_WRITE_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_NESTED_WRITE_DICTIONARY:-120}" "$seed" --nested-writes
check "member-result alias choice dictionary model fuzzing (${FUZZ_MODEL_RESULT_ALIAS_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_RESULT_ALIAS_DICTIONARY:-120}" "$seed" --result-aliases
check "named/default choice dictionary model fuzzing (${FUZZ_MODEL_NAMED_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_NAMED_DICTIONARY:-120}" "$seed" --named-methods
check "numeric field write choice dictionary model fuzzing (${FUZZ_MODEL_NUMERIC_WRITE_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_NUMERIC_WRITE_DICTIONARY:-120}" "$seed" --numeric-writes
check "indexed field write choice dictionary model fuzzing (${FUZZ_MODEL_INDEXED_WRITE_DICTIONARY:-120} programs)" \
  scripts/fuzz-model-heterogeneous.sh "${FUZZ_MODEL_INDEXED_WRITE_DICTIONARY:-120}" "$seed" --indexed-writes
check "source break model fuzzing (${FUZZ_MODEL_BREAKS:-60} programs)" \
  scripts/fuzz-model-breaks.sh "${FUZZ_MODEL_BREAKS:-60}" "$seed"
check "choice model fuzzing (${FUZZ_MODEL_MV:-140} programs, functions with several values too)" \
  scripts/fuzz-model-mv.sh "${FUZZ_MODEL_MV:-140}" "$seed"
check "generic functions with several values (${FUZZ_MODEL_GENERIC:-150} programs, against a model of the docs)" \
  scripts/fuzz-model-generic.sh "${FUZZ_MODEL_GENERIC:-150}" "$seed"
check "generic choice regression (omitted named argument in a <decides> wrapper)" \
  scripts/fuzz-model-generic.sh 1 20768200
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
