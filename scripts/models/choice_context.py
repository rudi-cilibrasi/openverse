#!/usr/bin/env python3
"""Independent choice ordering/rollback oracle across lexical source contexts."""
import argparse
from pathlib import Path
import random

p = argparse.ArgumentParser()
p.add_argument('seed', type=int)
p.add_argument('expected', type=Path)
p.add_argument('--control', action='store_true')
args = p.parse_args()
rng = random.Random(args.seed)
context = ['param', 'field', 'block', 'ctor', 'defer'][args.seed % 5]
consumer = ['composed', 'exclusive', 'first', 'lazy'][(args.seed // 5) % 4]
a, b = rng.randint(1, 4), rng.randint(1, 4)
da, db = rng.randint(1, 3), rng.randint(1, 3)
ma, mb = rng.randint(1, 3), rng.randint(1, 3)
ra, rb = rng.randrange(ma), rng.randrange(mb)
first = consumer in ['first', 'lazy']
av = list(range(a, -1, -1)) if consumer == 'lazy' else list(range(a, a + (2 if consumer == 'exclusive' else 4)))
bv = list(range(b, -1, -1)) if consumer == 'lazy' else list(range(b, b + (2 if consumer == 'exclusive' else 4)))
heap = total = count = 0
lines = ['start'] if context == 'defer' else []
for x in av:
    if x % ma != ra:
        continue
    if not first:
        heap += da  # This prefix commits before the B generator starts.
    for y in bv:
        if (x + y) % mb != rb:
            continue
        heap = da + db if first else heap + db
        total += x + y
        count += 1
        lines.append(f'row {x} {y} {total} {heap}')
        if first:
            break
    if first and count:
        break
lines += [f'finish {count} {total} {heap}', f'result {count + total + heap}']
args.expected.write_text('exit=0\n' + '\n'.join(lines) + '\n')

header = '''Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Lazy(N:int)<computes><decides>:int=
    N>=0
    N|Lazy[N-1]
cell:=class{var N:int=0}
'''
def producer(n):
    if consumer == 'lazy':
        return f'Lazy[{n}]'
    if consumer == 'exclusive':
        return f'Early({n})'
    return f'(Two({n})|Two({n+2}))'
clauses = f'A:={producer(a)},set H.N+={da},Mod[A,{ma}]={ra},B:={producer(b)},set H.N+={db},Mod[A+B,{mb}]={rb}'
body = 'H:=cell{}\nvar Total:int=0\nvar Count:int=0\n'
if first:
    body += f'''if({clauses},E:[]t=Concatenate()):
    set Total=A+B+E.Length
    set Count=1
    Print("row {{A}} {{B}} {{Total}} {{H.N}}")
'''
else:
    body += f'''R:=for({clauses}):
    E:[]t=Concatenate()
    set Total+=A+B+E.Length
    Print("row {{A}} {{B}} {{Total}} {{H.N}}")
    E.Length
set Count=R.Length
'''
body += 'Print("finish {Count} {Total} {H.N}")\nCount+Total+H.N'
expr = 'block:\n' + '\n'.join('    ' + s for s in body.splitlines())
if args.control:
    header += 'Evaluate(W:[]t where t:type):int=\n' + '\n'.join('    '+s for s in body.splitlines()) + '\n'
    expr = 'Evaluate(block{W:[]t=Concatenate();W})'
def expression_at(indent):
    return ('\n' + ' ' * indent).join(expr.splitlines())
value = rng.choice(['7', '"payload"', 'array{1,2}'])
if context == 'param':
    program = f'''Use(X:t,?Result:int={expression_at(4)} where t:type):int=Result
Main():void=Print("result {{Use({value})}}")'''
elif context == 'field':
    program = f'''box(t:type):=class:
    Data:t
    Result:int={expression_at(4)}
Make(X:t where t:type):box(t)=box(t){{Data:=X}}
Main():void=Print("result {{Make({value}).Result}}")'''
elif context == 'block':
    program = f'''box(t:type):=class:
    Data:t
    var Result:int=0
    block:
        set Result={expression_at(8)}
Make(X:t where t:type):box(t)=box(t){{Data:=X}}
Main():void=Print("result {{Make({value}).Result}}")'''
elif context == 'ctor':
    program = f'''box(t:type):=class{{Data:t;Result:int=0}}
Make<constructor>(X:t where t:type):=box(t):
    Data:=X
    Result:={expression_at(4)}
Main():void=Print("result {{Make({value}).Result}}")'''
else:
    program = f'''Use(X:t where t:type):void=
    defer:
        Result:={expression_at(8)}
        Print("result {{Result}}")
    Print("start")
Main():void=Use({value})'''
print(header + program)
