#!/usr/bin/env bash
# Loops inside loops in the metadata flow check (#761). A `for`'s search has a
# level per generator, each a loop inside the level before, and the check
# iterated every loop to a fixed point from its entry: 2^n passes of the
# innermost body for n levels, whatever the bodies do (sixteen generators took
# nine seconds, twenty minutes). A loop that an enclosing loop reaches again
# now resumes from its last stable head, in bodies with and without cleanups.
# Here: headers of thirty-two levels within the compiler's limit and within a
# count of passes that does not depend on the machine's load, a header past the
# eight levels a search with an exclusive choice was held to, and the Core
# models of what a resumed head must not lose.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
lake build
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
# header KIND N: a `for` of N generators, each with a source that writes.
header() {
  local kind="$1" n="$2" i gens
  echo 'Cell := class{var N:int = 0}'
  printf 'Src(S:Cell, V:int)<transacts>:[]int =\n    set S.N += 1\n    array{V}\n'
  printf 'C(S:Cell)<transacts><decides>:void =\n    S.N >= 0\n'
  printf 'Note(S:Cell)<transacts>:void =\n    set S.N += 1000\n'
  case "$kind" in
    exclusive) gens='X0 := if (C[S]) then (3 | 1) else (4 | 1)' ;;
    *) gens='X0 : Src(S, 1)' ;;
  esac
  for ((i = 1; i < n; i++)); do gens+=", X$i : Src(S, X$((i - 1)))"; done
  printf 'Run(S:Cell)<transacts>:void =\n'
  [[ "$kind" == cleanup ]] && printf '    defer:\n        Note(S)\n'
  printf '    for (%s):\n' "$gens"
  [[ "$kind" == body-cleanup ]] && printf '        defer:\n            Note(S)\n'
  printf '        Print("row {X%d} {S.N}")\n' "$((n - 1))"
  printf 'Main()<transacts>:void =\n    S := Cell{}\n    Run(S)\n    Print("state {S.N}")\n'
}
# Thirty-two levels took 2^32 passes; they take about 1,300 (quadratic in the
# levels: 376 for sixteen, 4,552 for sixty-four). The bound leaves room for a
# change of the lowering, none for a pass per level of each level.
for kind in plain cleanup body-cleanup exclusive; do
  header "$kind" 32 >"$tmp/$kind.verse"
  (ulimit -v 4194304; OPENVERSE_DEBUG=1 timeout 15 .lake/build/bin/openverse check "$tmp/$kind.verse") \
    >/dev/null 2>"$tmp/$kind.err"
  passes="$(sed -n 's/^metadata loop passes=//p' "$tmp/$kind.err" | sort -n | tail -n 1)"
  [[ -n "$passes" ]] || { echo "no pass count for $kind"; cat "$tmp/$kind.err"; exit 1; }
  if ((passes > 20000)); then echo "$kind: $passes loop passes for 32 levels"; exit 1; fi
  echo "loop nests: $kind header of 32 levels checked in $passes loop passes"
done
# Sixty-four levels, plain and searched through an exclusive choice.
for kind in plain exclusive; do
  header "$kind" 64 >"$tmp/$kind.verse"
  (ulimit -v 4194304; timeout 15 .lake/build/bin/openverse check "$tmp/$kind.verse") >/dev/null
done
# A header past eight levels follows the rule of a shorter one;
# scripts/test-verse.sh runs it against its expected output in both runtimes.
(ulimit -v 4194304; timeout 15 .lake/build/bin/openverse check tests/verse/for_exclusive_many_levels.verse) >/dev/null
out="$tmp/models"
if ! timeout 300 lake env lean -j1 --run tests/lean/MetadataLoopNests.lean >"$out" 2>&1; then
  cat "$out"; exit 1
fi
tail -n 1 "$out"
grep -qx '192 loop-nest policy classifications; 0 mismatches' "$out"
echo "loop nests: headers of 32 and 64 levels checked within 15s (4 GiB)"
