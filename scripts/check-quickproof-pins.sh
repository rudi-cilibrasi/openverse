#!/usr/bin/env bash
# Fail when a file that a QuickProof theorem depends on differs from the commit the theorem is
# about (COMMIT in proofs/quickproof/*/project/project.conf). Needs no QuickProof: it runs in
# scripts/check.sh. After changing a pinned file, re-check the project
# (scripts/check-quickproof.sh --check NAME) and update its COMMIT.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bad=0
for conf in "$root"/proofs/quickproof/*/project/project.conf; do
  name="$(basename "$(dirname "$(dirname "$conf")")")"
  commit="$(sed -n 's/^COMMIT=\([0-9a-f]*\).*/\1/p' "$conf")"
  code="$(sed -n 's/^CODE="\(.*\)"/\1/p' "$conf")"
  for f in $code; do
    if ! git -C "$root" diff --quiet "$commit" -- "$f" || ! git -C "$root" diff --quiet -- "$f"; then
      echo "pin check: $name: $f differs from its pinned commit ${commit:0:12}" >&2
      bad=1
    fi
  done
done
[[ $bad -eq 0 ]] && echo "pin check: every QuickProof dependency matches its pinned commit"
exit $bad
