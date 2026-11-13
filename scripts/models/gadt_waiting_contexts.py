#!/usr/bin/env python3
"""Waiting default consumers: independent ordering, state and cancellation oracle."""
import argparse
import pathlib
import random

parser = argparse.ArgumentParser()
parser.add_argument('seed', type=int)
parser.add_argument('expected', type=pathlib.Path)
parser.add_argument('--control', action='store_true')
args = parser.parse_args()
rng = random.Random(args.seed)
shape = ['top', 'method', 'view'][args.seed % 3]
mode = ['refined', 'ordinary', 'lazy', 'opened'][(args.seed // 3) % 4]
good = (args.seed // 12) % 2 == 0
cancel = (args.seed // 24) % 2 == 0
n = rng.randint(0, 2)
values = [n, n + 1] if good else [0]
if mode == 'ordinary':
    values = list(range(n, -1, -1)) + list(range(n + 1, -1, -1))
elif mode == 'lazy':
    values = [v + l for v in values for l in range(v, -1, -1)]
elif mode == 'opened':
    values = [n + 1, n + 2] if good else [0]
state = 10
lines = []
interrupted = cancel and len(values) > 1
for v in values[:1] if interrupted else values:
    state += v
    lines.append(f'body {state}')
if interrupted:
    lines.append(f'body {state}')
else:
    lines.append(f'after {state}')
lines += [f'source {state}', f'background {state}',
          f'result {-1 if interrupted else len(values)} state {state}']
args.expected.write_text('exit=0\n' + '\n'.join(lines) + '\n')
print('''pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
root:=class{}
extra(t:type):=class(root){X:t;C:int=4}
cell:=class{var N:int=0}
Id(X:t where t:type)<computes>:t=X
Values(P:pair(a,b) where a:type,b:type):[]int=for(V:=if(D:=dup[P])then(D.C|D.C+1)else 0):V
Opened(P:root):[]int=for(V:=if(D:=extra[P])then(D.C+Id(array{D.X}).Length|D.C+Id(array{D.X}).Length+1)else 0):V
Lazy(N:int)<computes><decides>:int=block{N>=0;N|Lazy[N-1]}''')
print(f'Global:root=extra(string){{X:="tag",C:={n}}}' if good else 'Global:root=root{}')
gen = 'V:Values(P)' if args.control else 'V:=if(D:=dup[P])then(D.C|D.C+1)else 0'
value = 'V'
if mode == 'ordinary':
    gen = f'V:=(Lazy[{n}]|Lazy[{n + 1}])'
elif mode == 'lazy':
    gen += ',L:=Lazy[V]'
    value = 'V+L'
elif mode == 'opened':
    gen = 'V:Opened(Global)' if args.control else 'V:=if(D:=extra[Global])then(D.C+Id(array{D.X}).Length|D.C+Id(array{D.X}).Length+1)else 0'
# Keep method declaration indentation explicit.
compact = 'block{branch{defer:Print("background {H.N}");Sleep(0.05);set H.N=10;Sleep(1.0)};R:=for(' + gen + '):block{defer:Print("body {H.N}");Sleep(0.1);E:[]a=Concatenate();set H.N+=' + value + '+E.Length;' + value + '};R.Length}'
header = f'Run(P:pair(a,b),H:cell,?N:int={compact} where a:type,b:type)<suspends>:int=N'
if shape == 'top':
    print(header)
    call = 'Run(P,H)'
else:
    if shape == 'view':
        print('holder:=interface{Run(P:pair(a,b),H:cell,?N:int=0 where a:type,b:type)<suspends>:int}')
    print('box(t:type):=class' + ('(holder)' if shape == 'view' else '') + ':\n    X:t')
    print('    ' + header.replace('Run(', 'Run<override>(' if shape == 'view' else 'Run('))
    print('Make():box(string)=box(string){X:="tag"}')
    # (a constant at the top level states its type, Book of Verse ch. 16)
    print('B:holder=Make()' if shape == 'view' else 'B:box(string)=Make()')
    call = 'B.Run(P,H)'
print(f'''Use(P:pair(a,b),H:cell where a:type,b:type)<suspends>:int=
    defer:Print("source {{H.N}}")
    R:={call}
    Print("after {{H.N}}")
    R
Main()<suspends>:void=
    H:=cell{{}}''')
actual = f'dup({"int" if rng.choice([False, True]) else "string"}){{C:={n}}}' if good else 'pair(int,string){}'
if cancel:
    print(f'    R:=race:\n        Use({actual},H)\n        block{{Sleep(0.15);-1}}')
else:
    print(f'    R:=Use({actual},H)')
print('    Print("result {R} state {H.N}")')
