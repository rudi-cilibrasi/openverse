#!/usr/bin/env bash
# Private-cell calls of functions on a call cycle, and loops inside loops, in the
# metadata flow check (#753): the compiler within its limit on a lazy array-loop
# return with a captured mutable local, the same output as its source control,
# and the Core models of the recursive summary.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
lake build
# The compiler's own limit: before #753 this ran for minutes.
program=tests/verse/multi_return_array_loop_capture_gadt
(ulimit -v 4194304; timeout 15 .lake/build/bin/openverse check "$program.verse") >/dev/null
# The control keeps the count in an object's field instead of a captured `var`,
# which needs no private cell. scripts/test-verse.sh runs both against these.
cmp "$program.expected" "${program}_control.expected"
(ulimit -v 4194304; timeout 15 .lake/build/bin/openverse check "${program}_control.verse") >/dev/null
out="$(mktemp)"; trap 'rm -f "$out"' EXIT
if ! timeout 120 lake env lean -j1 --run tests/lean/MetadataRecursiveContexts.lean >"$out" 2>&1; then
  cat "$out"; exit 1
fi
tail -n 1 "$out"
grep -qx '36 recursive-context policy classifications; 0 mismatches' "$out"
echo "recursive contexts: lazy array-loop return with a captured local checked within 15s (4 GiB)"
