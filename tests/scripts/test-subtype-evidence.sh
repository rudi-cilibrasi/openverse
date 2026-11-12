#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
make -s -C runtime build/cverse
lake env lean --run tests/lean/SubtypeEvidenceScopes.lean
lake env lean --run tests/lean/SubtypeEvidenceInputs.lean
lake env lean --run tests/lean/ChoiceBoundMethods.lean
lake env lean --run tests/lean/BoundMethodValues.lean
lake env lean --run tests/lean/CallableBounds.lean
lake env lean --run tests/lean/ContainerViews.lean
lake env lean --run tests/lean/SubtypeEvidence.lean "$out"
lake env lean --run tests/lean/SubtypeContainers.lean "$out"
lake env lean --run tests/lean/SubtypeRelations.lean "$out"
for name in evidence relocated state state-control cancel cancel-control materialized materialized-state materialized-cancel materialized-defaults materialized-entry receiver receiver-state receiver-state-control receiver-cancel receiver-cancel-control interior-state interior-state-control interior-cancel interior-cancel-control refined refined-control refined-state refined-state-control refined-cancel refined-cancel-control composed-helper composed-helper-control staged-helper staged-helper-control tuple-relation ordinary-state ordinary-state-control ordinary-relay ordinary-relay-control; do
  runtime/build/cverse "$out/$name.vbc" > "$out/$name.actual"
  diff -u "$out/$name.expected" "$out/$name.actual"
done
for name in container-state container-state-control container-cancel container-cancel-control container-map-order container-map-order-control container-map-key-order container-map-key-order-control; do
  runtime/build/cverse "$out/$name.vbc" > "$out/$name.actual"
  diff -u "$out/$name.expected" "$out/$name.actual"
done
for name in relation-state relation-state-control relation-cancel relation-cancel-control relation-discard-state relation-discard-state-control relation-discard-cancel relation-discard-cancel-control; do
  runtime/build/cverse "$out/$name.vbc" > "$out/$name.actual"
  diff -u "$out/$name.expected" "$out/$name.actual"
done
for name in relation-bottom-error relation-bottom-error-control; do
  status=0
  runtime/build/cverse "$out/$name.vbc" > "$out/$name.actual" 2> "$out/$name.stderr" || status=$?
  if [[ "$status" != 2 ]]; then
    printf '%s: expected user error exit 2, got %s\n' "$name" "$status" >&2
    exit 1
  fi
  diff -u "$out/$name.expected" "$out/$name.actual"
  if ! grep -qx 'error: user' "$out/$name.stderr"; then
    printf '%s: expected the same user error as the concrete control\n' "$name" >&2
    cat "$out/$name.stderr" >&2
    exit 1
  fi
done
echo "subtype dictionary C trace passed"
