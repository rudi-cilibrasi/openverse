#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
make -s -C runtime build/cverse
lake env lean --run tests/lean/SubtypeEvidence.lean "$out"
runtime/build/cverse "$out/evidence.vbc" > "$out/actual"
diff -u "$out/evidence.expected" "$out/actual"
echo "subtype dictionary C trace passed"
