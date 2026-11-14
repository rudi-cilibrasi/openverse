#!/usr/bin/env python3
"""Source-method lookup and transactional choice, modeled as ordered values.

An inherited base method increments a counter and prints. A failed filter
restores that counter and its output; successful filters and bodies commit.
Only a lazy producer's path to a first success survives. The actual receiver
is a grandchild with conflicting overrides, so virtual lookup would disagree
with the source method's super call. Generic fields exercise Self capture.
The method that calls (super:)Act is an overload of Act, Act(Probe:run_probe),
that overrides the base's: (super:)Act is only in an override of Act (the
Book's tests, Super.versetest: "super on another method").
"""
import itertools
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
rng = random.Random(seed)
mode = (seed // 8) % 4
string_call = rng.choice([False, True])
start = rng.randrange(-2, 3)
default = rng.randrange(0, 3)
bias = rng.randrange(0, 7)
limit = bias if string_call else start + default
high = rng.randrange(0, 7)
leaf_type, value = rng.choice([('int', '7'), ('string', '"payload"')])
call = '(super:)Act("limit")' if string_call else f'(super:)Act({start})'
lines = []
count = 0


def act():
    global count
    count += 1
    if string_call:
        return [f'str limit {count}']
    return [f'default {default}', f'act {start} {default} {count}']


print(f'''Note(N:int)<transacts>:int =
    Print("default {{N}}")
    N
Nat(N:int,Hi:int)<transacts><decides>:int =
    N<=Hi
    Print("visit {{N}}")
    N | Nat[N+1,Hi]
Two(N:int):int=N|N+1
run_probe := struct{{}}
base(t:type) := class:
    V:t
    Bias:int
    var Calls:int=0
    Act(N:int,?Add:int=Note({default}))<transacts>:int =
        set Calls+=1
        Print("act {{N}} {{Add}} {{Calls}}")
        N+Add
    Act(S:string)<transacts>:int =
        set Calls+=1
        Print("str {{S}} {{Calls}}")
        Bias
    Act(Probe:run_probe)<transacts>:void = {{}}
mid(u:type) := class(base(u)):
    Act<override>(N:int,?Add:int=Note(99))<transacts>:int = 999
    Act<override>(Probe:run_probe)<transacts>:void =''')

if mode == 0:
    print(f'''        var Seen:int=0
        if(X:=Nat[0,{high}],set Seen+=1,X>{call},E:[]u=array{{V}}):
            Print("win {{X}} {{Seen}} {{E.Length}}")
        Print("seen {{Seen}}")''')
    winner = next((x for x in range(high + 1) if x > limit), None)
    if winner is None:
        lines.append('seen 0')
    else:
        lines.extend(f'visit {x}' for x in range(winner + 1))
        lines.extend(act())
        lines.extend([f'win {winner} 1 1', 'seen 1'])
else:
    clause = 'A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2))'
    pairs = list(itertools.product(range(4), repeat=2))
    if mode == 1:
        print(f'''        var Seen:int=0
        if({clause},set Seen+=1,A+B>{call},E:[]u=array{{V}}):
            Print("win {{A}} {{B}} {{Seen}} {{E.Length}}")
        Print("seen {{Seen}}")''')
        winner = next(((a, b) for a, b in pairs if a + b > limit), None)
        if winner is None:
            lines.append('seen 0')
        else:
            lines.extend(act())
            lines.extend([f'win {winner[0]} {winner[1]} 1 1', 'seen 1'])
    elif mode == 2:
        print(f'''        for({clause},A+B>{call}):
            E:[]u=array{{V}}
            Print("body {{A}} {{B}} {{E.Length}}")''')
        for a, b in pairs:
            if a + b > limit:
                lines.extend(act())
                lines.append(f'body {a} {b} 1')
    else:
        print(f'''        for({clause}):
            E:[]u=array{{V}}
            Print("body {{A}} {{B}} {{{call}}} {{E.Length}}")''')
        for a, b in pairs:
            lines.extend(act())
            lines.append(f'body {a} {b} {limit} 1')

print(f'''leaf(v:type) := class(mid(v)):
    Act<override>(S:string)<transacts>:int=888
Main()<transacts>:void =
    L:=leaf({leaf_type}){{V:={value},Bias:={bias}}}
    L.Act(run_probe{{}})
    Print("calls {{L.Calls}}")''')
lines.append(f'calls {count}')
Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
