#!/usr/bin/env python3
"""Refined immediate event bodies retain subscription and failure boundaries."""
import argparse
from pathlib import Path
import random

p = argparse.ArgumentParser()
p.add_argument('seed', type=int)
p.add_argument('expected', type=Path)
p.add_argument('--control', action='store_true')
args = p.parse_args()
rng = random.Random(args.seed)
left, right = rng.choice([True, False]), rng.choice([True, False])
delta = rng.randint(1, 5)
modulus = rng.randint(1, 3)
remainder = rng.randrange(modulus)
limit = rng.choice([0, 1, 5, 9, 13])
values_a, values_b = ([4, 5] if left else [0]), ([7, 8] if right else [0])
lines = []
count = heap = total = 0
handlers = 1
failed = False
for a in values_a:
    for b in values_b:
        value = a + b
        if value % modulus != remainder:
            continue
        heap += delta
        count += 1
        handlers += 1
        for _ in range(handlers):
            total += value
            lines.append(f'heard {value} {total}')
        if value < limit:
            failed = True
            break
    if failed:
        break
if failed:
    # The source call is an if condition: its heap writes, subscriptions
    # and buffered callback output all roll back together (DESIGN.md).
    lines.clear()
    heap = total = 0
    handlers = 1
    lines.append('failed 0 0')
else:
    lines.append(f'success {count} {heap} {total}')
for _ in range(handlers):
    total += 9
    lines.append(f'heard 9 {total}')
lines.append(f'final {heap} {total}')
args.expected.write_text('exit=0\n' + '\n'.join(lines) + '\n')

print('''pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
listener := class:
    var Sum:int=0
    Add(N:int):void=
        set Sum+=N
        Print("heard {N} {Sum}")
Use(P:pair(a,b),Q:pair(c,d),H:cell,E:subscribable_event(int),L:listener where a:type,b:type,c:type,d:type)<decides>:int=
    var Count:int=0''')
clauses = ['A:=if(D:=dup[P])then(D.C|D.C+1)else 0',
           'B:=if(F:=dup[Q])then(F.C|F.C+1)else 0']
if args.control:
    clauses = ['A:=' + '|'.join(map(str, values_a)),
               'B:=' + '|'.join(map(str, values_b))]
clauses += [f'set H.N+={delta}', f'Mod[A+B,{modulus}]={remainder}']
print(f'''    for({','.join(clauses)}):
        set Count+=1
        C:=E.Subscribe(L.Add)
        E.Signal(A+B)
        A+B>={limit}
    Count
Main():void=
    E:=subscribable_event(int){{}}
    H:=cell{{}}
    L:=listener{{}}
    C:=E.Subscribe(L.Add)''')
pv = 'dup(int){A:=1,B:=2}' if left else 'pair(int,string){A:=1,B:="s"}'
qv = 'dup(string){A:="x",B:="y",C:=7}' if right else 'pair(string,int){A:="x",B:=2}'
print(f'''    if(R:=Use[{pv},{qv},H,E,L]):Print("success {{R}} {{H.N}} {{L.Sum}}")
    else:Print("failed {{H.N}} {{L.Sum}}")
    E.Signal(9)
    Print("final {{H.N}} {{L.Sum}}")''')
