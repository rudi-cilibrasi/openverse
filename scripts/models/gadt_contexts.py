#!/usr/bin/env python3
"""Refining choices in lexical/concurrent contexts, with an independent state oracle."""
import argparse
import pathlib
import random

p = argparse.ArgumentParser()
p.add_argument('seed', type=int)
p.add_argument('expected', type=pathlib.Path)
p.add_argument('--control', action='store_true')
args = p.parse_args()
rng = random.Random(args.seed)
contexts = ['parameter', 'field', 'constructor', 'block', 'defer', 'sync', 'race', 'rush', 'branch']
context = contexts[args.seed % len(contexts)]
mode = ['basic', 'first', 'for', 'lazy'][(args.seed // len(contexts)) % 4]
# Every 72 consecutive seeds cover both cast outcomes in all 36 modes.
good = (args.seed // 36) % 2 == 0
text = rng.choice([True, False])
n, boost = rng.randint(0, 5), rng.randint(1, 4)
modulus = rng.randint(1, 4)
remainder = rng.randrange(modulus)
opened = context == 'field'
if mode == 'lazy' and (args.seed // 72) % 2 == 0:
    n = -2 if opened else -1
value = n + int(opened)
values = [value, value + 1] if good else [0]
state = 0
if mode == 'basic':
    result = value if good else 0
    state = boost if good else 0
elif mode == 'for':
    selected = [v for v in values if v % modulus == remainder]
    result = sum(selected)
    state = (1 + boost) * len(selected)
else:
    values = list(range(value, -1, -1)) if good and mode == 'lazy' else values
    selected = next((v for v in values if v % modulus == remainder), None)
    result = -1 if selected is None else selected
    if selected is not None:
        state = 1 + (value - selected + 1 if good and mode == 'lazy' else 0)
checksum = 100 * state + result
args.expected.write_text('exit=0\n' + ('body\n' if context == 'defer' else '') + str(checksum) + '\n')
# (root and extra are <computes>: the constant Global constructs one, and a
# module's constant has no side effect, Book of Verse tests,
# DefaultValueAssignment.versetest:199)
print('''pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
root:=class<computes>{}
extra(t:type):=class<computes>(root){X:t;C:int=4}
cell:=class{var N:int=0}
Id(X:t where t:type)<computes>:t=X
NoneValue()<computes><decides>:int=block{false?;0}
Sum(Xs:[]int)<computes>:int=
    var Total:int=0
    for(V:Xs):set Total+=V
    Total
Lazy(H:cell,N:int)<transacts><decides>:int=
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]''')
if good:
    ty, literal = ('string', '"tag"') if text else ('int', '7')
    print(f'Global:root=extra({ty}){{X:={literal},C:={n}}}')
else:
    print('Global:root=root{}')
cast = 'D:=extra[Global]' if opened else 'D:=dup[P]'
branch = 'D.C+W.Length' + ('+Id(array{D.X}).Length' if opened else '')
if mode == 'basic':
    body = f'if({cast})then block{{set H.N+={boost};{branch}}}else 0'
    if args.control:
        body = f'block{{set H.N+={boost};{value}}}' if good else '0'
    tail = f'V:={body};100*H.N+V'
else:
    branch_values = f'Lazy[H,{branch}]' if mode == 'lazy' else f'({branch}|{branch}+1)'
    generator = f'if({cast})then {branch_values} else 0'
    clauses = f'V:={generator}'
    if args.control:
        clauses = 'V:=' + '|'.join(map(str, values)) if values else 'V:=NoneValue[]'
        if mode == 'lazy' and good:
            clauses += f',set H.N+={value}-V+1'
    clauses += f',set H.N+=1,Mod[V,{modulus}]={remainder}'
    if mode == 'for':
        tail = f'R:=for({clauses}):block{{set H.N+={boost};V}};100*H.N+Sum(R)'
    else:
        tail = f'R:=if({clauses})then V else -1;100*H.N+R'
expr = f'block{{H:=cell{{}};W:[]a=Concatenate();{tail}}}'
if context == 'parameter':
    print(f'Run(P:pair(a,b),?N:int={expr} where a:type,b:type):int=N')
    print('Use(P:pair(a,b) where a:type,b:type):int=Run(P)')
elif context == 'field':
    print(f'box(a:type,b:type):=class{{X:a;Y:b;N:int={expr}}}')
    print('Use(P:pair(a,b),X:a,Y:b where a:type,b:type):int=box(a,b){X:=X,Y:=Y}.N')
elif context == 'constructor':
    print('box(a:type,b:type):=class{Data:pair(a,b);N:int=0}')
    print(f'Make<constructor>(P:pair(a,b) where a:type,b:type):=box(a,b):\n    Data:=P\n    N:={expr}')
    print('Use(P:pair(a,b) where a:type,b:type):int=Make(P).N')
elif context == 'block':
    print(f'box(a:type,b:type):=class:\n    P:pair(a,b)\n    var N:int=0\n    block:set N={expr}')
    print('Use(P:pair(a,b) where a:type,b:type):int=box(a,b){P:=P}.N')
elif context == 'defer':
    print(f'Use(P:pair(a,b) where a:type,b:type):void=\n    defer:Print("{{{expr}}}")\n    Print("body")')
elif context == 'branch':
    print(f'Use(P:pair(a,b) where a:type,b:type)<suspends>:void=\n    branch:\n        Print("{{{expr}}}")\n        Sleep(0.1)\n    Sleep(0.2)')
else:
    result = 'R(0)' if context == 'sync' else 'R'
    print(f'Use(P:pair(a,b) where a:type,b:type)<suspends>:int=\n    R:={context}:\n        block:\n            N:={expr}\n            Sleep(0.1)\n            N\n        block:\n            Sleep(0.2)\n            -1\n    {result}')
actual = f'dup({"string" if text else "int"}){{C:={n}}}' if good else 'pair(int,string){}'
if context == 'field':
    actual = 'pair(int,string){},7,"s"'
call = f'Use({actual})'
body = call if context in ['defer', 'branch'] else f'Print("{{{call}}}")'
suspends = '<suspends>' if context in ['sync', 'race', 'rush', 'branch'] else ''
print(f'Main(){suspends}:void={body}')
