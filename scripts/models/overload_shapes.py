#!/usr/bin/env python3
"""Pinned overload-domain examples across callers, order and generic patterns.

The table is a source-language oracle, independent of elaborator representation.
Every contiguous default-size range covers each row, context and declaration
order. The seed also varies data and generic instantiations.
"""
from pathlib import Path
import random
import re
import sys


# (first type, second type, distinct, first argument, second argument,
#  optional b-is-a-subclass flag).
# Empty containers, int-indexed maps/options, unknown patterns and function
# signatures deliberately retain their overlap. Mixed tuple elements test
# that ONE distinct field suffices (not every field).
CASES = [
    ('tuple(a,b)', '[]a', True, '(A,B)', 'array{A}'),
    ('tuple(int,string)', '[]int', True, '(N,"s")', 'array{N}'),
    ('tuple(a)', '[logic]a', True, 'PA(A)', 'map{true=>A}'),
    ('tuple(int,int)', '[string]int', True, '(N,N)', 'map{"s"=>N}'),
    ('tuple(a)', '?a', True, 'PA(A)', 'option{A}'),
    ('tuple(a,b)', '?a', True, '(A,B)', 'option{A}'),
    ('tuple(a,t)', '[]b', True, '(A,N)', 'array{B}'),
    ('tuple(t,a)', '[]b', True, '(N,A)', 'array{B}'),
    ('tuple(int,t)', '[]string', True, '(N,N)', 'array{"s"}'),
    ('tuple(t)', '[logic]t', True, 'PN(N)', 'map{true=>N}'),
    ('tuple(a)', '?string', True, 'PA(A)', 'option{"s"}'),
    ('tuple()', '[]int', False, '()', 'array{}'),
    ('tuple()', '[logic]int', False, '()', 'map{}'),
    ('tuple()', '?string', False, '()', 'false'),
    ('tuple(a,b)', '[]a', False, '', '', True),
    ('tuple(int,int)', '[]rational', False, '', ''),
    ('tuple(int,int)', '[int]string', False, '', ''),
    ('tuple(a)', '[int]a', False, '', ''),
    ('tuple(int)', '?int', False, '', ''),
    ('tuple(a)', '?rational', False, '', ''),
    ('tuple(t)', '[]int', False, '', ''),
    ('tuple(a)', '[t]a', False, '', ''),
    ('tuple(a)', '?t', False, '', ''),
    ('[]int', '[string]string', False, '', ''),
    ('[]int', '[]string', False, '', ''),
    ('[int]int', '[string]string', False, '', ''),
    ('?int', '?string', False, '', ''),
    ('?int', 'logic', False, '', ''),
    ('[]string', 'logic', False, '', ''),
    ('type{_(:int)<computes>:int}', '[]string', False, '', ''),
    ('type{_(:string)<decides>:string}', '[int]int', False, '', ''),
    ('type{_(:int,:int)<computes>:int}', '[]int', False, '', ''),
    ('type{_(:int)<computes>:int}', 'type{_(:string)<computes>:string}', False, '', ''),
    ('int', 'rational', False, '', ''),
    # Retained surrounding domains: the new callable guard is specific to
    # arrays/maps; it must not reject ordinary classes or these other pairs.
    ('a', '[]int', True, 'A', 'array{N}'),
    ('a', '[logic]int', True, 'A', 'map{true=>N}'),
    # (a map and an option both have the empty value, `false`: they overlap
    # as an array and an option do, Book of Verse ch. 2)
    ('[logic]int', '?int', False, '', ''),
    ('type{_(:int)<computes>:int}', '?int', True, 'Scalar', 'option{N}'),
    ('type{_(:int)<computes>:int}', 'tuple(int,int)', True, 'Scalar', '(N,N)'),
]
CONTEXTS = ['top', 'named', 'generic', 'method', 'qualified', 'constructor', 'extension']
PERIOD = len(CASES) * len(CONTEXTS) * 2


def generate(seed):
    rng = random.Random(seed)
    index = (seed - 1) % PERIOD
    row = index % len(CASES)
    context = CONTEXTS[(index // len(CASES)) % len(CONTEXTS)]
    reverse = index // (len(CASES) * len(CONTEXTS))
    case = CASES[row]
    ta, tb, distinct, va, vb = case[:5]
    # A class-owned t is shared by both signatures, but t=void is a finite
    # comparable witness: map[logic]void also packs into tuple(void), erasing
    # its singleton element. Fixed tuple(int)/map[logic]int stays distinct.
    # Other contexts here retain an additional Hint/Extra positional formal
    # or match X by name, so their singleton argument is not repacked.
    if context in ('method', 'qualified') and (ta, tb) == ('tuple(t)', '[logic]t'):
        distinct = False
    related = len(case) > 5 and case[5]
    open_t = bool(re.search(r'\bt\b', ta + tb))
    tp = ['t:subtype(comparable)'] if open_t else []
    where = lambda ps: ' where ' + ','.join(ps) if ps else ''
    tclass = '(t:subtype(comparable))' if open_t else ''
    tparent = '(t)' if open_t else ''
    tactual = '(int)' if open_t else ''
    n = rng.randrange(2, 100)
    declarations = []
    header = f'''# row {row}, {context}, reverse {reverse}, seed {seed}
a:=class{{V:int={n}}}
b:=class{'(a)' if related else ''}{{W:int={n+1}}}
One(X:tuple(u) where u:type)<computes>:tuple(u)=X
Scalar(X:int)<computes>:int=X
'''
    calls = []
    expected = ['A', 'B']
    if context in ('top', 'generic', 'named'):
        tps = tp + (['u:type'] if context == 'generic' else [])
        for ty, label in [(ta, 'A'), (tb, 'B')]:
            params = (f'Extra:{"t" if open_t else "int"},?X:{ty},?D:int=4' if context == 'named'
                      else f'X:{ty}' + (',Extra:u' if context == 'generic' else '')
                      + (',Hint:t' if open_t else ''))
            declarations.append(f'F({params}{where(tps)}):string="{label}"')
        for value in [va, vb]:
            args = (f'{n},?X:={value}' if context == 'named' else value
                    + (f',{n}' if context == 'generic' else '')
                    + (f',{n}' if open_t and context != 'named' else ''))
            calls.append(f'Print(F({args}))')
    elif context in ('method', 'qualified'):
        prefix = '(i:)' if context == 'qualified' else ''
        header += f'i{tclass}:=interface:\n    F(X:{ta}):string\n    F(X:{tb}):string\n'
        parents = f'i{tparent}'
        if context == 'qualified':
            header += f'j{tclass}:=interface:\n    F(X:{ta}):string\n'
            parents += f',j{tparent}'
        header += f'base{tclass}:=class({parents}):\n'
        declarations = [f'    {prefix}F<override>(X:{ty}):string="{label}"'
                        for ty, label in [(ta, 'A'), (tb, 'B')]]
        if context == 'qualified':
            declarations.append(f'    (j:)F<override>(X:{ta}):string="J"')
        else:
            expected = ['A!', 'B']
        calls = [f'Obj:=base{tactual}{{}}' if context == 'qualified' else f'Obj:=low{tactual}{{}}',
                 f'I:i{tactual}=Obj', f'Print(I.F({va}))', f'Print(I.F({vb}))']
        if context == 'qualified':
            calls.append(f'Print(Obj.(j:)F({va}))')
            expected.append('J')
    elif context == 'extension':
        # extension methods (Book of Verse ch. 6), overloaded by their
        # receiver's type, which a type parameter's where may follow
        for ty, label in [(ta, 'A'), (tb, 'B')]:
            declarations.append(f'(X:{ty}{where(tp)}).F({"Hint:t" if open_t else ""}):string="{label}"')
        calls = [f'Print(({value}).F({n if open_t else ""}))' for value in [va, vb]]
    else:
        header += 'out:=class{Label:string}\n'
        declarations = [f'Make<constructor>(X:{ty}{",Hint:t" if open_t else ""}{where(tp)}) := out:\n    Label:="{label}"'
                        for ty, label in [(ta, 'A'), (tb, 'B')]]
        calls = [f'Print(Make({value}{","+str(n) if open_t else ""}).Label)' for value in [va, vb]]
    if reverse:
        declarations.reverse()
    program = header + '\n'.join(declarations) + '\n'
    if context == 'method':
        program += f'low{tclass}:=class(base{tparent}):\n    F<override>(X:{ta}):string="A!"\n'
    program += 'Main():void=\n'
    if distinct:
        program += f'''    N:int={n}
    A:=a{{}}
    B:=b{{}}
    PA:type{{_(:a)<computes>:tuple(a)}}=One
    PN:type{{_(:int)<computes>:tuple(int)}}=One
'''
        program += '\n'.join('    ' + c for c in calls) + '\n'
    else:
        program += '    {}\n'
    return program, {'exit': 0, 'stdout': '\n'.join(expected) + '\n'} if distinct else {
        'exit': 4, 'diagnostic': 'call cannot tell apart'}


if __name__ == '__main__':
    program, expected = generate(int(sys.argv[1]))
    print(program, end='')
    import json
    Path(sys.argv[2]).write_text(json.dumps(expected) + '\n')
