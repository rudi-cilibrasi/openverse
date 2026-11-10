#!/usr/bin/env bash
# Differential fuzzing of floats (#127): random Verse programs of float
# arithmetic, NaN and infinities, conversions, comparisons and ToString
# (scripts/gen-floats.py), run by the Lean reference interpreter and by
# cverse; both must print exactly what Python's IEEE doubles give under
# Verse's rules (the generator's expected output).
#   usage: scripts/fuzz-floats.sh [COUNT [FIRST_SEED [CVERSE]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec "$root/scripts/fuzz-expected.sh" floats "$root/scripts/gen-floats.py" \
  "${1:-200}" "${2:-1}" "${3:-$root/runtime/build/cverse}"
