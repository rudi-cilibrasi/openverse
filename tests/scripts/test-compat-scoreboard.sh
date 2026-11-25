#!/usr/bin/env bash
# Every conformance probe against Epic's recorded results (UEFN 43.12): fails on a difference that
# tests/conformance/versevm/known-differences.tsv does not list, on a listed probe that no longer
# differs, on a Lean/C disagreement, and when docs/COMPATIBILITY.md's generated parts are out of date.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
exec python3 -I tests/conformance/versevm/scoreboard.py --run --check --md docs/COMPATIBILITY.md
