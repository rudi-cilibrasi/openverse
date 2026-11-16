#!/usr/bin/env bash
# Run module-loading API checks before the native generated-program cap.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
lake env lean -j1 --run tests/lean/InitializerChoiceMetadata.lean "$out"
programs=("$out"/*.vbc)
[[ ${#programs[@]} == 16 ]]
for program in "${programs[@]}"; do
  (ulimit -v 4194304; timeout 15 runtime/build/cverse "$program") > "$out/actual" 2> "$out/stderr"
  cmp "${program%.vbc}.expected" "$out/actual"
  test ! -s "$out/stderr"
done
echo "initializer metadata C contracts passed (16 complete oracles)"
