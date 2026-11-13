#!/usr/bin/env bash
# The source acceptance suite of upper bounds (#502, docs/research/upper-bound-acceptance.md):
# exact Lean and C output oracles, specific refusals and admitted-bytecode comparisons for the
# fixtures in tests/upper-bounds. scripts/check.sh runs it; it prints a summary when every case
# passes, and everything when one does not.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
make -s -C runtime build/cverse
suite() {
  local status=0
  lake env lean --run tests/lean/UpperBoundSource.lean "$out" || status=$?
  for bytecode in "$out"/*.vbc; do
    [[ -e "$bytecode" ]] || continue
    name="${bytecode%.vbc}"
    runtime/build/cverse "$bytecode" > "$name.actual"
    if diff -u "$name.expected" "$name.actual"; then
      printf 'ok %s: C oracle\n' "${name##*/}"
    else
      status=1
    fi
  done
  return "$status"
}
if suite >"$out/log" 2>&1; then
  printf 'upper-bound source acceptance (#502): %s Lean and %s C oracles, %s refusals checked\n' \
    "$(grep -c ': checked Lean oracle$' "$out/log")" "$(grep -c ': C oracle$' "$out/log")" \
    "$(grep -c ': refused$' "$out/log")"
else
  cat "$out/log"
  exit 1
fi
