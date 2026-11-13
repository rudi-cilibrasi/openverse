#!/usr/bin/env bash
# The source acceptance suite of upper bounds (#502, docs/research/upper-bound-acceptance.md):
# exact Lean and C output oracles, specific refusals and admitted-bytecode comparisons for the
# fixtures in tests/upper-bounds. Run as it is, it is the evidence for admitting source bounds,
# for a checkout with the guard (UpperBounds.checkParams) relaxed: while the guard is in place
# it is expected to fail, each bounded fixture refused by the guard.
# With --guarded, as scripts/check.sh runs it, it asserts exactly the guarded refusals: the
# cases in tests/upper-bounds/guarded.list are refused by the guard, every other case passes as
# it would without the flag, and it prints a summary (everything, on a failure). When the guard
# goes, that list goes, and the gate runs the suite without --guarded.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
make -s -C runtime build/cverse
suite() {
  local status=0
  lake env lean --run tests/lean/UpperBoundSource.lean "$out" "$@" || status=$?
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
if [[ ${1:-} == --guarded ]]; then
  if suite --guarded >"$out/log" 2>&1; then
    printf 'upper-bound source acceptance (#502), guarded: %s cases refused by the guard as listed, %s Lean and %s C oracles, %s refusals checked\n' \
      "$(grep -c ': refused by the guard$' "$out/log")" "$(grep -c ': checked Lean oracle$' "$out/log")" \
      "$(grep -c ': C oracle$' "$out/log")" "$(grep -c ': refused$' "$out/log")"
  else
    cat "$out/log"
    exit 1
  fi
else
  suite
fi
