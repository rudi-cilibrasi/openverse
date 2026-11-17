#!/usr/bin/env bash
# Reuse the resource phase's checked bytecode after the C runtime is built.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
artifacts="${1:?expected metadata-reader artifact directory}"
shopt -s nullglob
programs=("$artifacts"/*.vbc)
if [[ ${#programs[@]} != 12 ]]; then
  echo "metadata-reader: expected 12 admitted waiting-function bytecode oracles" >&2
  exit 1
fi
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for program in "${programs[@]}"; do
  (ulimit -v 4194304; timeout 15 runtime/build/cverse "$program") >"$work/actual"
  diff -u "${program%.vbc}.expected" "$work/actual"
done
echo "metadata reader C-runtime contracts passed (12 complete 64-row-count oracles)"
