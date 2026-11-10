#!/usr/bin/env bash
# Differential fuzzing of choice (#208): random Verse programs whose `if`,
# `for` and `first{…}` clauses bind choices with effects and failures
# (scripts/gen-choice.py), run by the Lean reference interpreter and by
# cverse; both must print exactly what the generator's backtracking model
# of the semantics gives.
#   usage: scripts/fuzz-choice.sh [COUNT [FIRST_SEED [CVERSE]]]
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec "$root/scripts/fuzz-expected.sh" choice "$root/scripts/gen-choice.py" \
  "${1:-200}" "${2:-1}" "${3:-$root/runtime/build/cverse}"
