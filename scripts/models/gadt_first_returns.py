#!/usr/bin/env python3
"""First-success returns preserve rollback, producer prefixes and snapshots.

The return is in the branch of the if whose condition takes the first
success, its value bound by the condition's last clause: a return cannot
leave the condition, a failure context (the Book of Verse's tests,
`Reachability.versetest:12`). --control writes the producers without
choices."""
import argparse
from pathlib import Path
import random

p = argparse.ArgumentParser()
p.add_argument('seed', type=int)
p.add_argument('expected', type=Path)
p.add_argument('--control', action='store_true')
args = p.parse_args()
rng = random.Random(args.seed)
kind = args.seed % 3
stop = rng.choice([True, False])
base, cleanup = rng.randint(0, 5), rng.randint(0, 5)
da, db, dr = [rng.randint(1, 4) for _ in range(3)]
modulus = rng.randint(1, 5)
remainder = rng.randrange(modulus)
left, right = rng.choice([True, False]), rng.choice([True, False])
a, b = rng.randint(1, 4), rng.randint(1, 4)
if kind == 0:
    av, bv = list(range(a, a + 4)), list(range(b, b + 4))
elif kind == 1:
    av, bv = ([4, 5] if left else [0]), ([7, 8] if right else [0])
else:
    av, bv = list(range(a, -1, -1)), list(range(b, -1, -1))
chosen = next(((x, y) for x in av for y in bv if (x + y) % modulus == remainder), None)
total, heap, lines = base, 0, []
if chosen is not None:
    x, y = chosen
    total += x + y
    # Each retained recursive prefix runs once; rejected suffix writes roll back.
    producer_writes = (a - x + 1) + (b - y + 1) if kind == 2 else 0
    heap = producer_writes + da + db + (dr if stop else 0)
    lines.append(f'operand {x + y} {heap}' if stop else f'then {x + y} 0 {total} {heap}')
lines += [f'source {total + cleanup} {heap}',
          f'result {total} ' + ('payload' if args.seed % 2 else '9')]
args.expected.write_text('exit=0\n' + '\n'.join(lines) + '\n')

print('''pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){C:int=4}
cell:=class{var N:int=0}
Two(N:int)<computes>:int=N|N+1
Lazy(H:cell,N:int)<transacts><decides>:int=
    N>=0
    set H.N+=1
    N|Lazy[H,N-1]''')
print(f'''Value(H:cell,N:int,Total:int,Z:t,?E:[]t=Concatenate() where t:type)<transacts><decides>:tuple(int,t)=
    set H.N+={dr}
    Print("operand {{N}} {{H.N}}")
    Mod[N,{modulus}]={remainder}
    (Total+E.Length,Z)
Use(P:pair(a,b),Q:pair(c,d),Z:t where a:type,b:type,c:type,d:type,t:type)<transacts>:tuple(int,t)=
    H:=cell{{}}
    var Total:int={base}
    defer:
        set Total+={cleanup}
        Print("source {{Total}} {{H.N}}")''')
if kind == 0:
    prod_a, prod_b = f'(Two({a})|Two({a + 2}))', f'(Two({b})|Two({b + 2}))'
elif kind == 1:
    prod_a = 'if(D:=dup[P])then(D.C|D.C+1)else 0'
    prod_b = 'if(F:=dup[Q])then(F.C|F.C+1)else 0'
else:
    prod_a, prod_b = f'Lazy[H,{a}]', f'Lazy[H,{b}]'
if args.control and kind != 2:
    prod_a, prod_b = '|'.join(map(str, av)), '|'.join(map(str, bv))
clauses = [f'A:={prod_a}', f'set H.N+={da}', 'set Total+=A',
           f'B:={prod_b}', f'set H.N+={db}', 'set Total+=B']
if stop:
    # (the operand, bound by the condition's last clause, returned from the
    # branch: no clause after it runs)
    clauses += ['Returned:=Value[H,A+B,Total,Z]']
    branch = 'return Returned'
else:
    clauses += [f'Mod[A+B,{modulus}]={remainder}', 'After:[]t=Concatenate()']
    branch = 'Print("then {A+B} {After.Length} {Total} {H.N}")'
print(f'''    if({','.join(clauses)}):{branch}
    (Total,Z)
Main():void=''')
pv = 'dup(int){A:=1,B:=2}' if left else 'pair(int,string){A:=1,B:="s"}'
qv = 'dup(string){A:="x",B:="y",C:=7}' if right else 'pair(string,int){A:="x",B:=2}'
z = '"payload"' if args.seed % 2 else '9'
print(f'''    R:=Use({pv},{qv},{z})
    Print("result {{R(0)}} {{R(1)}}")''')
