#!/usr/bin/env python3
"""Immediate refined loops spawn generic calls; model task/cleanup ordering."""
import argparse
import pathlib
import random

p = argparse.ArgumentParser()
p.add_argument('seed', type=int)
p.add_argument('expected', type=pathlib.Path)
p.add_argument('--control', action='store_true')
args = p.parse_args()
rng = random.Random(args.seed)
left, right = rng.choice([True, False]), rng.choice([True, False])
increment, cleanup = rng.randint(1, 5), rng.randint(0, 3)
modulus = rng.randint(1, 3)
remainder = rng.randrange(modulus)
stop = rng.choice([0, 1, 2, 4])
text = rng.choice([True, False])
values_a, values_b = ([4, 5] if left else [0]), ([7, 8] if right else [0])
lines, started = [], []
total = count = heap = 0
returned = False
for a in values_a:
    for b in values_b:
        if (a + b) % modulus != remainder:
            continue
        heap += increment
        total += a + b
        count += 1
        started.append(a + b)
        lines.append(f'start {a + b} 0')
        saved = total
        total += cleanup
        lines.append(f'body {total}')
        if stop and count >= stop:
            returned = True
            break
    if returned:
        break
if not returned:
    lines.append(f'rows {count} {heap} {total}')
    saved = total
lines += [f'source {total} {heap}', f'result {saved}']
lines += [f'done {n} 0' for n in started]
lines.append(f'heap {heap}')
args.expected.write_text('exit=0\n' + '\n'.join(lines) + '\n')

print('''pair(a:type,b:type) := class { A:a;B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
cell := class { var N:int=0 }
Child(N:int,X:t,?E:[]t=Concatenate() where t:type)<suspends>:void=
    Print("start {N} {E.Length}")
    Sleep(0.5)
    Print("done {N} {E.Length}")
Use(P:pair(a,b),Q:pair(c,d),H:cell,Z:t where a:type,b:type,c:type,d:type,t:type)<transacts>:int=
    var Total:int=0
    var Count:int=0
    defer:Print("source {Total} {H.N}")''')
clauses = ['A:=if(D:=dup[P])then(D.C|D.C+1)else 0',
           'B:=if(F:=dup[Q])then(F.C|F.C+1)else 0']
if args.control:
    clauses = ['A:=' + '|'.join(map(str, values_a)),
               'B:=' + '|'.join(map(str, values_b))]
clauses += [f'set H.N+={increment}', f'Mod[A+B,{modulus}]={remainder}']
print(f'''    for({','.join(clauses)}):
        defer:
            set Total+={cleanup}
            Print("body {{Total}}")
        set Total+=A+B
        set Count+=1
        T:=spawn{{Child(A+B,Z)}}''')
if stop:
    print(f'        if(Count>={stop}):return Total')
print('''    Print("rows {Count} {H.N} {Total}")
    Total
Main()<suspends>:void=
    H:=cell{}''')
pv = 'dup(int){A:=1,B:=2}' if left else 'pair(int,string){A:=1,B:="s"}'
qv = 'dup(string){A:="x",B:="y",C:=7}' if right else 'pair(string,int){A:="x",B:=2}'
zv = '"z"' if text else '9'
print(f'''    R:=Use({pv},{qv},H,{zv})
    Print("result {{R}}")
    Sleep(1.0)
    Print("heap {{H.N}}")''')
