#!/usr/bin/env python3
"""Immediate refining consumers in a suspending source frame, from LANGUAGE.md.

Each real choice starts a filter snapshot. A rejected filter rolls back;
entering a later (possibly empty) generator commits that prefix. Bodies run
without yielding. A delayed observer then sees and updates the source local.
Some runs return from a body: save the operand, run body/source cleanup,
and cancel the pending observer when the source function ends.
Some put the consumer under an always-successful outer refining cast;
each body writes its current total to an object, observed at source exit.
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
ret_rng = random.Random(seed * 1000003 + 417437)
returning = bool(ret_rng.randrange(2))
body_cleanup, source_cleanup = ret_rng.randint(1, 7), ret_rng.randint(1, 7)
reachable = [(a, v, w, z) for a in [0, 1] for v in vs for w in ws for z in zs
             if v >= cut_v and w >= cut_w]
stop = ret_rng.choice([None] + reachable) if returning else None
scoped = bool(seed & 8)

out = []
total, count = start, 0
heap = 0
answer = None
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
                heap = total
                out.append(f'body {a} {v} {w} {z} {total}')
                if (a, v, w, z) == stop:
                    answer = total
                if returning:
                    total += body_cleanup
                    out.append(f'body cleanup {total}')
                if answer is not None:
                    break
            if answer is not None:
                break
        if answer is not None:
            break
    if answer is not None:
        break
if answer is None:
    out.append(f'rows {count} {total}')
    out.append(f'observe {total}')
    total += observer_step
    out.append(f'done {total}')
    answer = total
if returning:
    total += source_cleanup
    out.append(f'source cleanup {total}')
if scoped:
    out.append(f'heap {heap}')
out.append(f'result {answer}')
Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(out) + '\n')
p = 'dup(int){A:=1,B:=2}' if p_hit else 'pair(int,string){A:=1,B:="s"}'
q = 'dup(string){A:="a",B:="b"}' if q_hit else 'pair(string,int){A:="a",B:=2}'
z_source = 'array{' + ','.join(map(str, zs)) + '}'
source_defer = (f'    defer:\n        set Total+={source_cleanup}\n'
                '        Print("source cleanup {Total}")\n') if returning else ''
body_defer = (f'        defer:\n            set Total+={body_cleanup}\n'
              '            Print("body cleanup {Total}")\n') if returning else ''
condition = ','.join(f'{n}={v}' for n, v in zip(['A', 'V', 'W', 'Z'], stop)) if stop else 'A=-99'
return_clause = f'        if({condition}):return Total\n' if returning else ''
heap_stamp = '        Stamp(H,Total)\n' if scoped else ''
consumer = f'''    Zs:[]int={z_source}
    R:=for(A:=0|1,set Total+=A,Print("outer {{A}} {{Total}}"),
        V:=if(D:=dup[P])then(D.C|D.C+1)else(0|1),
        set Total+=V,Print("v {{A}} {{V}} {{Total}}"),V>={cut_v},
        W:=if(E:=dup[Q])then(E.C|E.C+1)else(0|1),
        set Total+=W,Print("w {{A}} {{V}} {{W}} {{Total}}"),W>={cut_w},Z:Zs):
{body_defer}        Empty:[]t=Concatenate()
        var Local:int=A
        if(F:=dup[P]):
            Value:b=F.A
            set Local+={nested_step}
        set Total+=Local-A+{body_step}+Z+Empty.Length
{heap_stamp}        Print("body {{A}} {{V}} {{W}} {{Z}} {{Total}}")
{return_clause}        Total
    Print("rows {{R.Length}} {{Total}}")
    Sleep(0.2)
    Print("done {{Total}}")
    Total
'''
if scoped:
    consumer = consumer.removesuffix('    Total\n') + '    return Total\n'
    consumer = '    if(Scoped:=dup[Scope]):\n' + ''.join('    ' + line for line in consumer.splitlines(True)) + '    -1\n'
scope_param = ',Scope:pair(sx,sy)' if scoped else ''
scope_types = ',sx:type,sy:type' if scoped else ''
scope_arg = ',dup(int){A:=0,B:=0,C:=0}' if scoped else ''
heap_prelude = 'stamp := class { var N:int=0 }\nStamp(H:stamp,N:int)<writes>:void = set H.N=N\n' if scoped else ''
heap_setup = '    H:=stamp{}\n    defer:Print("heap {H.N}")\n' if scoped else ''
print(f'''pair(a:type,b:type) := class {{ A:a; B:b }}
dup(t:type) := class(pair(t,t)) {{ C:int }}
{heap_prelude}Run(P:pair(a,b),Q:pair(c,d),Unused:t{scope_param} where a:type,b:type,c:type,d:type,t:type{scope_types})<suspends>:int =
    var Total:int={start}
{heap_setup}{source_defer}    branch:
        Sleep(0.1)
        Print("observe {{Total}}")
        set Total+={observer_step}
    Sleep(0.0)
{consumer}Main()<suspends>:void =
    P:={p.replace('}',f',C:={pc}}}') if p_hit else p}
    Q:={q.replace('}',f',C:={qc}}}') if q_hit else q}
    Print("result {{Run(P,Q,{rng.choice(['7', '"s"'])}{scope_arg})}}")
''')
