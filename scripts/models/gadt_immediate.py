#!/usr/bin/env python3
"""Immediate refining consumers in a suspending source frame, from LANGUAGE.md.

Each real choice starts a filter snapshot. A rejected filter rolls back;
entering a later (possibly empty) generator commits that prefix. Bodies run
without yielding. A delayed observer then sees and updates the source local.
The model enumerates these snapshots independently of frontend helpers.
"""
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
rng = random.Random(seed)
p_hit, q_hit = rng.choice([False, True]), rng.choice([False, True])
pc, qc = rng.randint(2, 5), rng.randint(2, 5)
cut_v, cut_w = rng.randint(0, 6), rng.randint(0, 6)
start, body_step, nested_step, observer_step = [rng.randint(1, 7) for _ in range(4)]
zs = list(range(rng.randint(0, 2)))
vs = [pc, pc + 1] if p_hit else [0, 1]
ws = [qc, qc + 1] if q_hit else [0, 1]

out = []
total, count = start, 0
for a in [0, 1]:
    # The cast's selected arm always starts a real choice, keeping this prefix.
    total += a
    out.append(f'outer {a} {total}')
    for v in vs:
        if v < cut_v:
            continue
        total += v
        out.append(f'v {a} {v} {total}')
        for w in ws:
            if w < cut_w:
                continue
            total += w
            out.append(f'w {a} {v} {w} {total}')
            for z in zs:
                if p_hit:
                    total += nested_step
                total += body_step + z
                count += 1
                out.append(f'body {a} {v} {w} {z} {total}')
out.append(f'rows {count} {total}')
out.append(f'observe {total}')
total += observer_step
out.append(f'done {total}')
out.append(f'result {total}')
Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(out) + '\n')
p = 'dup(int){A:=1,B:=2}' if p_hit else 'pair(int,string){A:=1,B:="s"}'
q = 'dup(string){A:="a",B:="b"}' if q_hit else 'pair(string,int){A:="a",B:=2}'
z_source = 'array{' + ','.join(map(str, zs)) + '}'
print(f'''pair(a:type,b:type) := class {{ A:a; B:b }}
dup(t:type) := class(pair(t,t)) {{ C:int }}
Run(P:pair(a,b),Q:pair(c,d),Unused:t where a:type,b:type,c:type,d:type,t:type)<suspends>:int =
    var Total:int={start}
    branch:
        Sleep(0.1)
        Print("observe {{Total}}")
        set Total+={observer_step}
    Sleep(0.0)
    Zs:[]int={z_source}
    R:=for(A:=0|1,set Total+=A,Print("outer {{A}} {{Total}}"),
        V:=if(D:=dup[P])then(D.C|D.C+1)else(0|1),
        set Total+=V,Print("v {{A}} {{V}} {{Total}}"),V>={cut_v},
        W:=if(E:=dup[Q])then(E.C|E.C+1)else(0|1),
        set Total+=W,Print("w {{A}} {{V}} {{W}} {{Total}}"),W>={cut_w},Z:Zs):
        Empty:[]t=Concatenate()
        var Local:int=A
        if(F:=dup[P]):
            Value:b=F.A
            set Local+={nested_step}
        set Total+=Local-A+{body_step}+Z+Empty.Length
        Print("body {{A}} {{V}} {{W}} {{Z}} {{Total}}")
        Total
    Print("rows {{R.Length}} {{Total}}")
    Sleep(0.2)
    Print("done {{Total}}")
    Total
Main()<suspends>:void =
    P:={p.replace('}',f',C:={pc}}}') if p_hit else p}
    Q:={q.replace('}',f',C:={qc}}}') if q_hit else q}
    Print("result {{Run(P,Q,{rng.choice(['7', '"s"'])})}}")
''')
