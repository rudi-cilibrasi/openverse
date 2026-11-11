#!/usr/bin/env python3
"""Source-loop model for for filters: break crosses producers; failure rolls back.

Some immediate consumers select their lazy sources under independent
refining casts. Both actual receivers hit, so the source-loop oracle and
the existing random program distribution stay unchanged.
"""
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
rng = random.Random(seed)
na, nb = rng.randint(-1, 3), rng.randint(-1, 3)
cut_a, cut_b = rng.randint(0, 3), rng.randint(0, 3)
refs_a, refs_b = rng.choice([False, True]), rng.choice([False, True])
suspends, used = rng.choice([False, True]), rng.choice([False, True])
waits = suspends and rng.choice([False, True])
refined = bool(seed & 8) and not waits
body_delta, filter_delta, loop_delta, fn_delta = [rng.randint(1, 7) for _ in range(4)]
reachable = [(a, b) for a in range(na, -1, -1) for b in range(nb, -1, -1)
             if a >= cut_a and b >= cut_b]
stop = rng.choice([-1] + [a * 10 + b for a, b in reachable])

# Each real generator begins its own filter snapshot. No producer effects.
total = field = count = 0
out = []
stopped = False
for a in range(na, -1, -1):
    before_a = total, field, len(out)
    total += a
    field += a + 1
    out.append(f"a {a} {total} {field}")
    if a < cut_a:
        total, field, size = before_a
        del out[size:]
        continue
    for b in range(nb, -1, -1):
        before_b = total, field, len(out)
        total += b
        field += b + 1
        out.append(f"b {b} {total} {field}")
        if b < cut_b:
            total, field, size = before_b
            del out[size:]
            continue
        if a * 10 + b == stop:
            total += filter_delta
            field += filter_delta
            out.append(f"filter cleanup {total} {field}")
            stopped = True
            break
        out.append(f"keep {a} {b}")
        total += body_delta
        field += body_delta
        out.append(f"local cleanup {total} {field}")
        out.append(f"body {a} {b} {total} {field}")
        count += 1
    if stopped:
        break
if not stopped:
    out.append(f"completed {count if used else field}")
total += loop_delta
field += loop_delta
out.append(f"loop cleanup {total} {field}")
answer = total
total += fn_delta
field += fn_delta
out.append(f"function cleanup {total} {field}")
out.append(f"result {answer} {field}")
Path(sys.argv[2]).write_text("exit=0\n" + "".join(line + "\n" for line in out))

pre = '''counter := class:
    var N:int = 0
Lazy(N:int)<computes><decides>:int =
    N >= 0
    N | Lazy[N-1]
RefLazy(N:int)<transacts><decides>:counter =
    N >= 0
    counter{N:=N} | RefLazy[N-1]
'''
if refined:
    pre += 'pair(a:type,b:type) := class {}\ndup(t:type) := class(pair(t,t)) { C:int }\n'
source_a = f"{'RefLazy' if refs_a else 'Lazy'}[{na}]"
if refined:
    source_a = f"if(D:=dup[P])then {'RefLazy' if refs_a else 'Lazy'}[D.C]else {source_a}"
clauses = [f"{'EA' if refs_a else 'A'} := {source_a}"]
if refs_a:
    clauses.append("A := EA.N")
clauses += ["set Total += A", "set H.N += A + 1", 'Print("a {A} {Total} {H.N}")', f"A >= {cut_a}"]
source_b = f"{'RefLazy' if refs_b else 'Lazy'}[{nb}]"
if refined:
    source_b = f"if(E:=dup[Q])then {'RefLazy' if refs_b else 'Lazy'}[E.C]else {source_b}"
clauses.append(f"{'EB' if refs_b else 'B'} := {source_b}")
if refs_b:
    clauses.append("B := EB.N")
clauses += ["set Total += B", "set H.N += B + 1", 'Print("b {B} {Total} {H.N}")', f"B >= {cut_b}",
            f'''if (A * 10 + B = {stop}):
                defer:
                    set Total += {filter_delta}
                    set H.N += {filter_delta}
                    Print("filter cleanup {{Total}} {{H.N}}")
                break
            else:
                Print("keep {{A}} {{B}}")''']
body = f'''loop:
                defer: Print("local cleanup {{Total}} {{H.N}}")
                set Total += {body_delta}
                set H.N += {body_delta}
                break
'''
if waits:
    body += '            Sleep(0.0)\n'
body += '            Print("body {A} {B} {Total} {H.N}")\n            (A, B)'
mode = '<suspends>' if suspends else '<transacts>'
loop = ("R := " if used else "") + f"for ({', '.join(clauses)}):\n            {body}"
finish = 'R.Length' if used else 'H.N'
params = ',P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type' if refined else ''
args = f',dup(int){{C:={na}}},dup(string){{C:={nb}}}' if refined else ''
print(pre + f'''Run(H:counter{params}){mode}:int =
    var Total:int = 0
    defer:
        set Total += {fn_delta}
        set H.N += {fn_delta}
        Print("function cleanup {{Total}} {{H.N}}")
    loop:
        defer:
            set Total += {loop_delta}
            set H.N += {loop_delta}
            Print("loop cleanup {{Total}} {{H.N}}")
        {loop}
        Print("completed {{{finish}}}")
        if ({stop} >= 0):
            Err()
        break
    Total
Main(){mode}:void =
    H := counter{{}}
    Print("result {{Run(H{args})}} {{H.N}}")
''')
