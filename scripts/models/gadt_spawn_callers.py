#!/usr/bin/env python3
"""Immediate callers around a task start, from ordinary call semantics.

The child has narrow effects (<computes>, <reads> or <allocates>); a spawn
has <transacts>'s, besides its call's (the Book's tests, Effects.versetest:
"spawn requires the transacts effect in addition to the effects of the
spawned async function"), so the function that spawns, and every caller up
to Main, is <transacts>. The wrappers do not wait or change user state.
Starting the child reaches its first wait before returning the task.
--direct emits the control without the wrappers; its trace and RNG draws
are identical.
"""
import json
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
rng = random.Random(seed)
style = seed % 5
fx = ("computes", "reads", "allocates")[(seed // 5) % 3]
string = bool((seed // 15) % 2)
cancel = bool((seed // 30) % 2)
n, initial, depth = rng.randint(1, 40), rng.randint(1, 20), rng.randint(1, 4)
value = f"v{seed}" if string else n + 50
literal = json.dumps(value)
lines = [f"start {n}"]
if fx == "reads":
    lines.append(f"read {initial}")
elif fx == "allocates":
    lines.append(f"alloc {n}")
lines.append(f"created {initial}")
if cancel:
    lines += [f"cleanup {n}", f"cancelled {initial + 100}"]
else:
    if fx == "reads":
        lines.append(f"late {initial + 100}")
    lines += [f"end {n}", f"cleanup {n}", f"result {value} {initial + 100}"]
Path(sys.argv[2]).write_text("exit=0\n" + "\n".join(lines) + "\n")

print(f'''cell:=class{{var N:int=0}}
token:=class<allocates><unique>{{V:int}}
Child(H:cell,X:t,N:int where t:type)<suspends><{fx}>:t=
    defer:Print("cleanup {{N}}")
    Print("start {{N}}")''')
if fx == "reads":
    print('    Print("read {H.N}")')
elif fx == "allocates":
    print('    Obj:=token{V:=N}\n    Print("alloc {Obj.V}")')
print('    Sleep(0.1)')
if fx == "reads":
    print('    Print("late {H.N}")')
print('    Print("end {N}")\n    X')
# (the callers: <transacts>, as the spawn at the bottom is)
params = "H:cell,X:t,N:int where t:type"
call = "H,X,N"
start = f'Start({params})<transacts>:task(t)=spawn{{Child({call})}}'
if "--direct" in sys.argv[3:]:
    print(start)
    entry = "Start"
else:
    entry = "Entry"
    if style == 0:
        print(f'''Entry({params})<transacts>:task(t)=Middle({call})
Middle({params})<transacts>:task(t)=Start({call})''')
    elif style == 1:
        print(f'''Entry({params})<transacts>:task(t)=B({call},{depth})
B(H:cell,X:t,N:int,D:int where t:type)<transacts>:task(t)=A(H,X,N,D)
A(H:cell,X:t,N:int,D:int where t:type)<transacts>:task(t)=
    if(D<=0):return Start(H,X,N)
    B(H,X,N,D-1)''')
    elif style == 2:
        print(f'''iface(t:type):=interface<computes>:
    Launch(H:cell,X:t,N:int)<transacts>:task(t)
carrier(t:type):=class<computes>(iface(t)):
    Launch<override>(H:cell,X:t,N:int)<transacts>:task(t)=Start(H,X,N)
Entry({params})<transacts>:task(t)=
    B:iface(t)=carrier(t){{}}
    B.Launch({call})''')
    elif style == 3:
        print(f'''Entry({params})<transacts>:task(t)=
    F:type{{_(:cell,:t,:int)<transacts>:task(t)}}=Start
    F({call})''')
    else:
        print(f'''Entry({params})<transacts>:task(t)=Named(H,X)
Named(H:cell,X:t,?N:int={n} where t:type)<transacts>:task(t)=Start({call})''')
    print(start)
print(f'''Main()<suspends>:void=
    H:=cell{{N:={initial}}}
    T:={entry}(H,{literal},{n})
    Print("created {{H.N}}")
    set H.N={initial + 100}''')
if cancel:
    print('    T.Cancel()\n    Print("cancelled {H.N}")')
else:
    print('    V:=T.Await()\n    Print("result {V} {H.N}")')
