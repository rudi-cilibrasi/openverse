#!/usr/bin/env python3
"""Named defaults under selected class instances, independent of lowering.

The model evaluates supplied names in written order, then absent defaults
in declaration order. Defaults may depend on prior arguments and receiver
state; rejected first-success candidates restore that state and their output.
Other cases open hidden value types through a viewed interface.
"""
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
rng = random.Random(seed)
mode = (seed // 9) % 4
k, delta, x = rng.randrange(1, 8), rng.randrange(1, 5), rng.randrange(0, 8)
lines = []

if mode == 0:
    supplied = rng.choice([[], [('A', 20)], [('B', 30)], [('B', 30), ('A', 20)]])
    args = ''.join(f',?{n}:=Note("given-{n}",{v})' for n, v in supplied)
    print(f'''Note(S:string,N:int)<transacts>:int=block{{Print("{{S}} {{N}}");N}}
base(t:type) := class:
    F(X:t,?A:int=0,?B:int=0)<computes>:int=A+B
ib := class(base(int)):
    var Calls:int=0
    Seed:int={k}
    F<override>(X:int,?A:int=block{{set Calls+=1;Note("a",X+Seed)}},?B:int=Note("b",A+{delta}))<computes>:int=
        Print("body {{X}} {{A}} {{B}}")
        A+B
Run(P:base(a),X:a where a:type)<transacts>:int=P.F(X{args})
Main()<transacts>:void=
    C:=ib{{}}
    Print("result {{Run(C,{x})}}")
    Print("calls {{C.Calls}}")''')
    values = {}
    for name, value in supplied:
        lines.append(f'given-{name} {value}')
        values[name] = value
    calls = 0
    if 'A' not in values:
        calls += 1
        values['A'] = x + k
        lines.append(f'a {values["A"]}')
    if 'B' not in values:
        values['B'] = values['A'] + delta
        lines.append(f'b {values["B"]}')
    lines += [f'body {x} {values["A"]} {values["B"]}', f'result {sum(values.values())}', f'calls {calls}']
elif mode in (1, 2):
    ty, value = rng.choice([('int', '7'), ('string', '"payload"')])
    default = 'Concatenate()' if rng.choice([True, False]) else 'array{}'
    if mode == 1:
        print(f'''container(t:type) := interface:
    Get(Z:t,?Extra:t):t
k(a:type) := class(container([]a)):
    X:a
    Get<override>(Z:[]a,?Extra:[]a={default}):[]a=Z+Extra+array{{X}}
Run(P:container(u),D:u where u:type):u=P.Get(D)
Main():void=
    R:=Run(k({ty}){{X:={value}}},array{{{value}}})
    Print("length {{R.Length}}")''')
        lines = ['length 2']
    else:
        print(f'''leading(t:type) := interface:
    Tag():t
sink(t:type) := interface:
    F(?N:int=0):int
both(a:type,b:type) := class(leading(a),sink(b)):
    V:a
    Seed:int={k}
    Tag<override>():a=V
    F<override>(?N:int=block{{E:[]b={default};E.Length+Seed}}):int=N
Run(P:sink(u) where u:type):int=P.F()
Main():void=Print("result {{Run(both(int,{ty}){{V:=1}})}}")''')
        lines = [f'result {k}']
else:
    cutoff = rng.randrange(-1, 6)
    print(f'''base(t:type) := class:
    Pick(X:t,?D:int=0)<computes>:int=D
ib := class(base(int)):
    var Calls:int=0
    Pick<override>(X:int,?D:int=block{{set Calls+=1;Print("default {{X}}");X+{k}}})<computes>:int=D
Two():int=0|1|2|3
Run(P:base(a),X:a where a:type)<transacts>:void=
    if(I:=Two(),V:=P.Pick(X),I>{cutoff}):Print("win {{I}} {{V}}")
Main()<transacts>:void=
    C:=ib{{}}
    Run(C,{x})
    Print("calls {{C.Calls}}")''')
    winner = next((i for i in range(4) if i > cutoff), None)
    if winner is not None:
        lines = [f'default {x}', f'win {winner} {x+k}', 'calls 1']
    else:
        lines = ['calls 0']

Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
