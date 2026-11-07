#!/usr/bin/env bash
# Everything that needs no QuickProof: the Lean proofs and front end, the C runtime and its tests,
# both implementations on the Verse test suite, differential fuzzing, and the QuickProof pins.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
echo "== lake build (Lean proofs, front end, reference interpreter)"
lake build 2>&1 | tail -1
if grep -rnE '\bsorry\b|\badmit\b' OpenVerse/ Main.lean; then echo "error: sorry/admit in Lean sources" >&2; exit 1; fi
scripts/gen-claims.sh --check
echo "== C runtime"
make -s -C runtime test
echo "== Verse test suite, Lean and C"
scripts/test-verse.sh --c
echo "== differential fuzzing (${FUZZ:-1000} random programs)"
scripts/fuzz-diff.sh "${FUZZ:-1000}" 1
echo "== front-end mutation fuzzing (${FUZZ_FRONT:-500} mutants)"
scripts/fuzz-front.sh "${FUZZ_FRONT:-500}" 1
echo "== heap-reclamation fuzzing (${FUZZ_FIELDS:-60} programs with array fields)"
scripts/fuzz-fields.sh "${FUZZ_FIELDS:-60}" 1
echo "== QuickProof pins"
scripts/check-quickproof-pins.sh
echo "check.sh: all checks passed"
