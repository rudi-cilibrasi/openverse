#!/usr/bin/env bash
# A program gets the helpers written in Verse that its source asks for, and no
# others (`admitSource`, step 3): the rationals' for `/` or `rational`,
# ReplaceAll's for ReplaceAll. An attribute on an expression asks for none: the
# program compiles to the bytes it would without it.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ov="$root/.lake/build/bin/openverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
fail() { echo "helper-needs: $*" >&2; exit 1; }
# helpers NAME SOURCE: the helper functions (`$name`) of SOURCE's Verse Core
helpers() {
  printf '%b' "$2" >"$tmp/$1.verse"
  "$ov" core "$tmp/$1.verse" | sed -n 's/^fn [0-9]* \(\$[A-Za-z]*\) .*/\1/p' | tr '\n' ' '
}
[[ "$(helpers rational 'Main():void =\n    if (1 / 3 = 2 / 6) then Print("equal")\n')" == '$ratGcd $ratMake $ratLt ' ]] ||
  fail 'a program that divides has no rational helpers'
[[ "$(helpers replace 'Main():void = Print("abab".ReplaceAll("a", "c"))\n')" == '$replaceAll ' ]] ||
  fail 'a program that uses ReplaceAll has helpers other than its own'
[[ "$(helpers ignored 'Main():void =\n    X := @ignore_unreachable 1\n    Print("{X}")\n')" == '' ]] ||
  fail 'a program with @ignore_unreachable has helpers'
printf 'Main():void =\n    X := @ignore_unreachable 1\n    Print("{X}")\n' >"$tmp/with.verse"
printf 'Main():void =\n    X := 1\n    Print("{X}")\n' >"$tmp/without.verse"
"$ov" emit "$tmp/with.verse" -o "$tmp/with.vbc"
"$ov" emit "$tmp/without.verse" -o "$tmp/without.vbc"
cmp -s "$tmp/with.vbc" "$tmp/without.vbc" || fail '@ignore_unreachable changes the bytecode'
echo 'helper-needs: each program has the helpers it asks for'
