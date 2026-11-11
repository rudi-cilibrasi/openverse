#!/usr/bin/env python3
"""Comparable evidence from class membership (#209), modeled from LANGUAGE.md.

Types carry an algebraic comparability rule; successful membership supplies
only the target's declared bounds. Arrays/options/maps/tuples/value structs
need their components, while unique references need no argument bounds.
The model chooses concrete base/derived objects and predicts scalar dispatch,
ordered multiple results, cast conditions, failed conditions, and empty joins.
It also emits generic definitions that must be rejected even if never called.
No compiler/frontend helpers are used to calculate the expected result.
"""
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
rng = random.Random(seed)
case = seed // 6

# A set means these variables must be comparable; None means impossible.
def needs(t):
    kind, *args = t
    if kind == 'var':
        return {args[0]}
    if kind == 'unique':
        return set()
    if kind == 'plain':
        return None
    parts = [needs(a) for a in args]
    return None if any(p is None for p in parts) else set().union(*parts)


def syntax(t):
    kind, *args = t
    if kind == 'var':
        return args[0]
    if kind in ('int', 'string', 'plain'):
        return kind
    if kind in ('arr', 'opt'):
        return ('[]' if kind == 'arr' else '?') + syntax(args[0])
    if kind == 'map':
        return '[int]' + syntax(args[0])
    if kind == 'tuple':
        return 'tuple(' + ','.join(map(syntax, args)) + ')'
    return ('holder' if kind == 'unique' else 'wrap') + '(' + syntax(args[0]) + ')'


v = ('var', 't')
shapes = [v, ('arr', v), ('opt', v), ('map', v),
          ('tuple', ('arr', v), ('opt', v), ('map', v)), ('value', v), ('unique', v)]
shape = shapes[case % len(shapes)]
leaf = rng.choice(['int', 'string', 'plain'])


def closed(t):
    return (leaf,) if t[0] == 'var' else (t[0], *(closed(a) for a in t[1:]))


def literal(t, n):
    kind, *args = t
    if kind == 'int':
        return str(n), str(n)
    if kind == 'string':
        return f'"v{n}"', f'v{n}'
    if kind == 'plain':
        return f'plain{{V:={n}}}', f'plain:{n}'
    if kind == 'arr':
        x, shown = literal(args[0], n)
        return f'array{{{x}}}', '[' + shown + ']'
    if kind == 'opt':
        x, shown = literal(args[0], n)
        return f'option{{{x}}}', '?' + shown
    if kind == 'map':
        x, shown = literal(args[0], n)
        return f'map{{1=>{x}}}', 'map(1=>' + shown + ')'
    if kind == 'tuple':
        xs = [literal(a, n + i) for i, a in enumerate(args)]
        return '(' + ','.join(x for x, _ in xs) + ')', '(' + ','.join(s for _, s in xs) + ')'
    x, shown = literal(args[0], n)
    return syntax(t) + '{V:=' + x + '}', ('unique:' if kind == 'unique' else 'wrap:') + shown


show_defs = []
def shower(t):
    name = 'Show' + str(len(show_defs))
    show_defs.append('')
    kind, *args = t
    if kind == 'int':
        body = '"{X}"'
    elif kind == 'string':
        body = 'X'
    elif kind == 'plain':
        body = '"plain:{X.V}"'
    elif kind == 'arr':
        sh = shower(args[0])
        body = f'if(Y:=X[0]) then "[{{{sh}(Y)}}]" else "[]"'
    elif kind == 'opt':
        sh = shower(args[0])
        body = f'if(Y:=X?) then "?{{{sh}(Y)}}" else "none"'
    elif kind == 'map':
        sh = shower(args[0])
        body = f'if(Y:=X[1]) then "map(1=>{{{sh}(Y)}})" else "empty"'
    elif kind == 'tuple':
        shs = [shower(a) for a in args]
        body = '"(' + ','.join('{' + sh + f'(X({i}))' + '}' for i, sh in enumerate(shs)) + ')"'
    else:
        sh = shower(args[0])
        body = '"' + ('unique:' if kind == 'unique' else 'wrap:') + '{' + sh + '(X.V)}"'
    show_defs[int(name[4:])] = f'{name}(X:{syntax(t)}):string = {body}'
    return name


added = bool(case % 2)
extra = ',u:subtype(comparable)' if added else ''
field = '\n    E:u' if added else ''
local = 'W:[]u=Concatenate(); ' if added else ''
condition = 'V=V,W=W' if added else 'V=V'
source = f'''NeedCmp(X:a,Y:a where a:subtype(comparable))<decides>:void = X = Y
holder(t:type) := class<unique> {{ V:t }}
wrap(t:type) := struct {{ V:t }}
plain := class {{ V:int }}
root(z:type) := class:
    A:z
    B:z
    Hit(N:z,?Q:[]z=Concatenate()):int = 0
    Both(?Q:[]z=Concatenate()):z = A | B
tight(z:subtype(comparable){extra}) := class(root(z)):{field}
    Hit<override>(N:z,?Q:[]z=block{{V:[]z=Concatenate(); {local}if({condition}) then V else V}}):int = if(A=N) then 1 else 2
    Both<override>(?Q:[]z=block{{V:[]z=Concatenate(); {local}if({condition}) then V else V}}):z = if(A=A) then (B | A) else A
Get(P:root(z) where z:type):[]z = for(V:=P.Both()) {{ V }}
Empty(V:a where a:type)<decides>:a =
    false?
    V
'''

# Negative controls express facts not implied by the class test.
mode = (case // len(shapes)) % 5
if mode == 4:
    negative = case % 4
    if negative == 0:
        body = 'if(D:=tight[P]) then 0 else block{if(NeedCmp[V,V]) then 1 else 2}'
    elif negative == 1:
        body = 'block{if(D:=tight[P]) then 0 else 1; if(NeedCmp[V,V]) then 1 else 2}'
    elif negative == 2:
        if not needs(shape):
            shape = v
        body = 'block{Vs:=for(X:=if(D:=tight[P]) then(D.A|D.A) else Empty[P.A]){X}; if(NeedCmp[Vs,Vs]) then 1 else 2}'
    else:
        shape = ('unique', v)
        body = 'if(D:=tight[P]) then block{if(NeedCmp[V,V]) then 1 else 2} else 0'
    source += f'Reject(P:root({syntax(shape)}),V:t where t:type):int = {body}\nMain():void = Print("unused")\n'
    expected = 'exit=4\nmust be comparable\n'
else:
    cmp = 'NeedCmp[P.A,P.A]'
    if 't' in needs(shape):
        cmp += ',NeedCmp[V,V]'
    source += f'''Native(P:root({syntax(shape)}),V:t,K:int where t:type):int =
    var Total:int = 0
    if(D:=tight[P],{cmp},K>0,set Total+=K) then Total else Total+10
Joined(P:root({syntax(shape)}),V:t where t:type):int =
    Vs:=for(X:=if(D:=tight[P]) then(D.A|D.A) else Empty[P.A]){{X}}
    Vs.Length
'''
    ty = closed(shape)
    sh = shower(ty)
    source += '\n'.join(show_defs) + '\nMain():void =\n'
    lines = []
    for i in range(rng.randint(3, 6)):
        derived = i % 2 == 0 and needs(ty) == set()
        a, av = literal(ty, rng.randint(1, 8))
        b, bv = literal(ty, rng.randint(9, 16))
        value, _ = literal((leaf,), rng.randint(1, 8))
        name = f'P{i}'
        own = 'tight' if derived else 'root'
        args = syntax(ty) + (',string' if derived and added else '')
        ef = ',E:="extra"' if derived and added else ''
        source += f'    {name}:={own}({args}){{A:={a},B:={b}{ef}}}\n'
        k = rng.choice([-2, 0, 1, 3])
        source += f'    Print("{{Native({name},{value},{k})}} {{Joined({name},{value})}} {{{name}.Hit({name}.A)}}")\n'
        # Membership supplies evidence in that branch; a failed later clause
        # takes the else with the initial local state.
        lines.append(f'{k if derived and k > 0 else 10} {2 if derived else 0} {1 if derived else 0}')
        source += f'    for(X:Get({name})){{Print({sh}(X))}}\n'
        lines.extend([bv, av] if derived else [av, bv])
    expected = 'exit=0\n' + '\n'.join(lines) + '\n'

print(source, end='')
Path(sys.argv[2]).write_text(expected)
