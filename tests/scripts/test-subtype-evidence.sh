#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
make -s -C runtime build/cverse
lake env lean --run tests/lean/SubtypeEvidence.lean "$out"
for name in evidence relocated state state-control cancel cancel-control materialized materialized-state materialized-cancel materialized-defaults materialized-entry receiver receiver-state receiver-state-control receiver-cancel receiver-cancel-control; do
  runtime/build/cverse "$out/$name.vbc" > "$out/$name.actual"
  diff -u "$out/$name.expected" "$out/$name.actual"
done
echo "subtype dictionary C trace passed"
