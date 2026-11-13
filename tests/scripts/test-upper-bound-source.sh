#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
make -s -C runtime build/cverse
status=0
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
exit "$status"
