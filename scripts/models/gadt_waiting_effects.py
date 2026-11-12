#!/usr/bin/env python3
"""Source heap effects through nested refining waiting loops.

The oracle follows two generator values and a wait in each body. --plain
uses the explicit generator values under the same outer refinements.
"""
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
fxs = [("reads",), ("allocates",), ("writes",),
       ("reads", "allocates"), ("reads", "writes"),
       ("allocates", "writes"), ("reads", "allocates", "writes")]
fx = fxs[seed % 7]
depth = (seed // 7) % 3
first = bool((seed // 21) % 2)
cancel = bool((seed // 42) % 2)
base = random.Random(seed).randint(5, 25)
state = base
lines = ["start 4", f"created {base}"]
if cancel:
    lines += ["cleanup 4", f"cancelled {base}"]
else:
    result = 0
    for v in (4, 5):
        if v == 5:
            lines.append("start 5")
        value = (state if "reads" in fx else base) + v
        if "writes" in fx:
            state = value
        lines += [f"done {v} {value}", f"cleanup {v}"]
        if first:
            result = value
            break
    lines.append(f"result {result} {state}")
Path(sys.argv[2]).write_text("exit=0\n" + "\n".join(lines) + "\n")

specs = "".join(f"<{f}>" for f in fx)
print(f'''pair(a:type,b:type):=class{{}}
dup(t:type):=class(pair(t,t)){{C:int=4}}
cell:=class{{var N:int=0}}
token:=class<allocates><unique>{{V:int}}
Use(P:pair(a,b),Q:pair(c,d),S:pair(e,f),H:cell,B:int where a:type,b:type,c:type,d:type,e:type,f:type)<suspends>{specs}:int=''')
indent = "    "
for i in range(depth):
    print(indent + f'if(Outer{i}:=dup[{("P", "Q")[i]}]):')
    indent += "    "
inner = ("P", "Q", "S")[depth]
generator = "array{4,5}" if "--plain" in sys.argv[3:] else f"if(D:=dup[{inner}])then(D.C|D.C+1)else 0"
binding = ':' if '--plain' in sys.argv[3:] else ':='
print(indent + f'for(V{binding}{generator}):')
indent += "    "
print(indent + 'defer:Print("cleanup {V}")')
print(indent + 'Print("start {V}")')
print(indent + 'Sleep(0.1)')
value = "H.N+V" if "reads" in fx else "B+V"
if "allocates" in fx:
    print(indent + f'Obj:=token{{V:={value}}}')
    value = "Obj.V"
print(indent + f'Out:={value}')
if "writes" in fx:
    print(indent + 'set H.N=Out')
print(indent + 'Print("done {V} {Out}")')
if first:
    print(indent + 'return Out')
print('    0')
print(f'''Main()<suspends>:void=
    H:=cell{{N:={base}}}
    T:=spawn{{Use(dup(int){{}},dup(string){{}},dup(char){{}},H,{base})}}
    Print("created {{H.N}}")''')
if cancel:
    print('    Sleep(0.05)\n    T.Cancel()\n    Print("cancelled {H.N}")')
else:
    print('    R:=T.Await()\n    Print("result {R} {H.N}")')
