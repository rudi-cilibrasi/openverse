#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
make -s -C runtime build/cverse
lake env lean --run tests/lean/SubtypeEvidenceScopes.lean
lake env lean --run tests/lean/SubtypeEvidence.lean "$out"
lake env lean --run tests/lean/SubtypeContainers.lean "$out"
for name in evidence relocated state state-control cancel cancel-control materialized materialized-state materialized-cancel materialized-defaults materialized-entry receiver receiver-state receiver-state-control receiver-cancel receiver-cancel-control interior-state interior-state-control interior-cancel interior-cancel-control refined refined-control refined-state refined-state-control refined-cancel refined-cancel-control composed-helper composed-helper-control staged-helper staged-helper-control tuple-relation ordinary-state ordinary-state-control ordinary-relay ordinary-relay-control; do
  runtime/build/cverse "$out/$name.vbc" > "$out/$name.actual"
  diff -u "$out/$name.expected" "$out/$name.actual"
done
for name in container-state container-state-control container-cancel container-cancel-control container-map-order container-map-order-control container-map-key-order container-map-key-order-control; do
  runtime/build/cverse "$out/$name.vbc" > "$out/$name.actual"
  diff -u "$out/$name.expected" "$out/$name.actual"
done
echo "subtype dictionary C trace passed"
