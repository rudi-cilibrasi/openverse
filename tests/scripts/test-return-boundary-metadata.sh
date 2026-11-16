#!/usr/bin/env bash
# Compiler API admission loads Lean modules before the generated-program cap.
# The C artifacts retain the same fixed native execution budget.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
lake env lean -j1 --run tests/lean/ReturnBoundaries.lean "$out"
printf '1\n' > "$out/expected"
programs=("$out"/*.vbc)
[[ ${#programs[@]} == 8 ]]
for program in "${programs[@]}"; do
  (ulimit -v 4194304; timeout 15 runtime/build/cverse "$program") > "$out/actual" 2> "$out/stderr"
  cmp "$out/expected" "$out/actual"
  test ! -s "$out/stderr"
done
echo "return boundary metadata contracts passed (12 classifications, 8 complete C oracles)"
