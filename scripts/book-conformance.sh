#!/usr/bin/env bash
# Measure openverse against the Book of Verse's own tests, Tests/**/*.versetest
# of a checkout of https://github.com/verselang/book at the pinned revision
# (docs/research/book-test-conformance.md says how each case is translated).
#
#   scripts/book-conformance.sh run BOOK [--results FILE] [--causes] [--jobs N] [--only SUBSTR]
#   scripts/book-conformance.sh compare BOOK      # against tests/conformance/book/baseline.tsv
#   scripts/book-conformance.sh baseline BOOK     # rewrite the baseline
#   scripts/book-conformance.sh show BOOK CASE    # the program a case becomes
#
# Needs `lake build` and `make -C runtime` first, and no network. It is not part
# of scripts/check.sh: the gate does not need the Book checkout.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$root/tests/conformance/book/booktests.py" "$@"
