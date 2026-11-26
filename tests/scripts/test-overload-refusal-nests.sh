#!/usr/bin/env bash
# Nested calls that no overload fits (#769). A call of an overloaded function
# asks for each of its arguments several times: alone, at each candidate's
# parameter type, again for the types its error names, and once more where a
# call of one argument is retried with a tuple's elements. An argument that is
# refused was refused each time, and one that is itself such a call made all of
# its own attempts again: five times the work at each level, so the six levels
# of tests/errors/overload_nested_unmatched took four tenths of a second, ten
# took two minutes, and the twenty-four of tests/verse/overload_char_string's
# call, without the overload its innermost argument fits, did not end. A
# refusal is now kept with its error (`ESt.refusals`, which outlives the failed
# attempt), and each is made once.
# Here: every shape of such a nest that took a multiple of its time per level,
# twenty-four and forty-eight levels deep, refused with the error the short nest
# is refused with, within a limit that is a guard against never ending and no
# measure of speed (a nest of twenty-four takes a third of a second; before,
# the quickest of these shapes took more than twice as long per level).
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ov="$root/.lake/build/bin/openverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
limit="${OVERLOAD_REFUSAL_TIMEOUT:-60}"
python3 -I - "$tmp" <<'PY'
import sys
out = sys.argv[1]
def nest(n, inner, wrap):
    e = inner
    for _ in range(n): e = wrap(e)
    return e
D = 'Depth(S:string):int = 0\nDepth(C:char):int = 2\n'
N = 'N(S:string, ?K:int = 0):int = 0\nN(C:char, ?K:int = 0):int = 2\n'
W = 'W(X:int):int = 1\nW(X:[]int):int = 2\nOne(X:tuple(u) where u:type)<computes>:tuple(u)=X\n'
P = '    P:type{_(:int)<computes>:tuple(int)} = One\n'
V = ("vec2i := struct{X:int, Y:int}\noperator'*'(L:vec2i, R:int):vec2i = L\n"
     "operator'*'(L:int, R:vec2i):vec2i = R\noperator'*'(L:char, R:char):char = L\n")
A = '    A := vec2i{X := 1, Y := 2}\n'
def main(e, pre=''): return 'Main():void =\n' + pre + '    Print("{%s}")\n' % e
def bind(e, pre=''): return 'Main():void =\n' + pre + '    Y := ' + e + '\n'
# name: (the program of n levels, its refusal)
def shapes(n):
    return {
        # the reduced program, and the form of the fixture's call
        'function': (D + main(nest(n, '1', lambda e: f'Depth({e})')),
                     'no overload of Depth takes (int)'),
        'three-overloads': (D + 'Depth(F:float):int = 3\n' + main(nest(n, '1', lambda e: f'Depth({e})')),
                            'no overload of Depth takes (int)'),
        'method': ('c := class:\n    M(S:string):int = 0\n    M(C:char):int = 2\n'
                   + main(nest(n, '1', lambda e: f'X.M({e})'), '    X := c{}\n'),
                   'no overload of M takes (int)'),
        # the receiver of each call is the call before it
        'method-receiver': ('c := class:\n    M(S:string):c = Self\n    M(C:char):c = Self\n'
                            + bind('X' + '.M(1)' * n, '    X := c{}\n'),
                            'no overload of M takes (int)'),
        'constructor': ('k := class:\n    V:int = 0\nMk<constructor>(S:string) := k{V := 0}\n'
                        'Mk<constructor>(C:char) := k{V := 2}\n' + main(nest(n, '1', lambda e: f'Mk({e}).V')),
                        'no overload of Mk takes (int)'),
        # the refused argument is not the only one, or not the first
        'first-of-two': ('F(S:string, A:int):int = 0\nF(C:char, A:int):int = 2\n'
                         + main(nest(n, '1', lambda e: f'F({e}, 0)')), 'no overload of F takes (int, int)'),
        'second-of-two': ('F(A:int, S:string):int = 0\nF(A:int, C:char):int = 2\n'
                          + main(nest(n, '1', lambda e: f'F(0, {e})')), 'no overload of F takes (int, int)'),
        # named arguments: beside the refused one, omitted, and the refused one itself
        'named-beside': (N + main(nest(n, '1', lambda e: f'N({e}, ?K := 1)')),
                         'no overload of N takes (int, ?K:int)'),
        'default-omitted': (N + main(nest(n, '1', lambda e: f'N({e})')), 'no overload of N takes (int)'),
        'named-refused': (N + main(nest(n - 1, 'N(1)', lambda e: f'N("a", ?K := {e})')),
                          'no overload of N takes (int)'),
        # the refused argument inside a tuple, an array and an operator's operand
        'tuple': ('T(P:tuple(int, string)):int = 0\nT(P:tuple(int, char)):int = 2\n'
                  + main(nest(n, '1', lambda e: f'T((0, {e}))')), 'no overload of T takes (tuple(int, int))'),
        'array': ('Ar(S:[]string):int = 0\nAr(C:float):int = 2\n'
                  + main(nest(n, '1', lambda e: f'Ar(array{{{e}}})')), 'no overload of Ar takes ([]int)'),
        'sum': (D + main(nest(n, '1', lambda e: f'Depth({e} + 1)')), 'no overload of Depth takes (int)'),
        # through a function that is not overloaded
        'plain-function': (D + 'Id(X:int):int = X\n' + main(nest(n, '1', lambda e: f'Depth(Id({e}))')),
                           'no overload of Depth takes (int)'),
        # the program's own operators, the refused operand on either side
        'operator-left': (V + bind(nest(n, 'true', lambda e: f'(({e}) * A)'), A),
                          "no overload of operator'*' takes (logic, vec2i)"),
        'operator-right': (V + bind(nest(n, 'true', lambda e: f'(A * ({e}))'), A),
                           "no overload of operator'*' takes (vec2i, logic)"),
        # the innermost error is another: two overloads fit, a name is unknown, a
        # plain call's argument; and the innermost call can fail, outside a failure
        # context (which is said of the statement, were its calls to fit)
        'ambiguous': (W + main(nest(n - 1, 'W(P(1))', lambda e: f'W({e})'), P),
                      'this call of W fits more than one overload: (int) and ([]int)'),
        'ambiguous-inside': (W + D + main(nest(n - 1, 'W(P(1))', lambda e: f'Depth({e})'), P),
                             'this call of W fits more than one overload: (int) and ([]int)'),
        'unknown-name': (D + main(nest(n, 'Nowhere', lambda e: f'Depth({e})')), "unknown identifier 'Nowhere'"),
        'failable': (D + 'Fa(X:int)<decides><transacts>:string =\n    X > 0\n    "a"\n'
                     + main(nest(n, 'Fa[1]', lambda e: f'Depth({e})')), 'no overload of Depth takes (int)'),
        'plain-mismatch': (D + 'Pl(S:string):int = 0\n' + main(nest(n - 1, 'Pl(1)', lambda e: f'Depth({e})')),
                           'expected string, found int'),
    }
for n in (3, 12, 16, 24, 48):
    for name, (program, refusal) in shapes(n).items():
        open(f'{out}/{name}.{n}.verse', 'w').write(program)
        open(f'{out}/{name}.want', 'w').write(refusal + '\n')
PY
count=0
for short in "$tmp"/*.3.verse; do
  name="$(basename "$short" .3.verse)"
  # the short nest's refusal, without its place: the nests differ in that only
  (cd "$tmp" && timeout "$limit" "$ov" check "$name.3.verse") >/dev/null 2>"$tmp/$name.3.err" && {
    echo "FAIL overload refusal nests: $name of 3 levels is accepted"; exit 1; }
  sed 's/^[^:]*:[0-9]*:[0-9]*: //' "$tmp/$name.3.err" >"$tmp/$name.3.msg"
  if ! grep -qF -f "$tmp/$name.want" "$tmp/$name.3.msg"; then
    echo "FAIL overload refusal nests: $name of 3 levels, wanted '$(cat "$tmp/$name.want")', got:"
    cat "$tmp/$name.3.err"; exit 1
  fi
  # (a chain of receivers is slower by the square of its length, a second
  # for twelve calls, which took 2.3 times longer per call before)
  deep=(24 48); [[ $name == method-receiver ]] && deep=(12 16)
  for n in "${deep[@]}"; do
    status=0
    (cd "$tmp" && ulimit -v 4194304 && timeout "$limit" "$ov" check "$name.$n.verse") \
      >/dev/null 2>"$tmp/$name.$n.err" || status=$?
    sed 's/^[^:]*:[0-9]*:[0-9]*: //' "$tmp/$name.$n.err" >"$tmp/$name.$n.msg"
    if [[ $status != 4 ]] || ! cmp -s "$tmp/$name.3.msg" "$tmp/$name.$n.msg"; then
      echo "FAIL overload refusal nests: $name of $n levels, status $status (124: not within ${limit}s)," \
        "wanted '$(cat "$tmp/$name.3.msg")', got:"
      head -c 400 "$tmp/$name.$n.err"; exit 1
    fi
  done
  count=$((count + 1))
done
# The call that fits, as deep: tests/verse/overload_char_string has it at
# twenty-four levels and scripts/test-verse.sh runs it in both runtimes.
python3 -I - "$tmp/fits.verse" <<'PY'
import sys
e = '1'
for _ in range(96): e = f'Depth({e})'
open(sys.argv[1], 'w').write('Depth(X:int):int = X + 1\nDepth(S:string):int = 0\nDepth(C:char):int = 2\n'
                             'Main():void =\n    Print("{%s}")\n' % e)
PY
(ulimit -v 4194304; timeout "$limit" "$ov" run "$tmp/fits.verse") >"$tmp/fits.out"
[[ "$(cat "$tmp/fits.out")" == 97 ]] || { echo "FAIL overload refusal nests: the nest that fits printed $(cat "$tmp/fits.out")"; exit 1; }
echo "overload refusal nests: $count shapes of 24 and 48 levels refused as at 3 levels, each within ${limit}s"
