#!/usr/bin/env python3
"""Spawned defaults: caller-order effects followed by task-body execution.

The model binds supplied names in written order, computes omitted defaults in
declaration order, and predicts output and counters without inspecting lowering.
--control generates an equivalent direct-method call for a pre-change compiler.
"""
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
rng = random.Random(seed)
control = '--control' in sys.argv[3:]
mode = rng.randrange(3)
lines = []
suspends = '<suspends>' if rng.choice([True, False]) else ''
ty, value = rng.choice([('int', str(rng.randrange(1, 10))), ('string', '"payload"')])

if mode == 0:
    base, x, delta, extra = [rng.randrange(1, 10) for _ in range(4)]
    names = [n for n in 'ABC' if rng.choice([True, False])]
    rng.shuffle(names)
    values = {n: rng.randrange(10, 30) for n in names}
    supplied = ''.join(f',?{n}:=Note("given {n}",{values[n]})' for n in names)
    recv = 'impl(z)' if control else 'base(u)'
    params = 'z:type' if control else 'u:type'
    xty = 'int' if control else 'u'
    print(f'''Note(S:string,N:int):int=block{{Print("{{S}} {{N}}");N}}
Tick(S:string,X:t where t:type):t=block{{Print(S);X}}
base(t:type) := class:
    Go(X:t,?A:int=0,?B:int=0,?C:int=0)<suspends><computes>:int=0
impl(z:type) := class(base(int)):
    Marker:z
    Seed:int={base}
    var Calls:int=0
    Go<override>(X:int,?A:int=block{{set Calls+=1;Note("default A",Seed+X)}},?B:int=block{{set Calls+=1;Note("default B",A+{delta})}},?C:int=block{{set Calls+=1;Note("default C",B+{extra})}})<suspends><computes>:int=
        Print("body {{X}} {{A}} {{B}} {{C}}")
        Sleep(0.001)
        A+B+C
Start(P:{recv},X:{xty} where {params}){suspends}:task(int)=spawn{{Tick("receiver",P).Go(Tick("positional",X){supplied})}}
Main()<suspends>:void=
    C:=impl({ty}){{Marker:={value}}}
    T:=Start(C,{x})
    Print("created {{C.Calls}}")
    Print("result {{T.Await()}} {{C.Calls}}")''')
    lines = ['receiver', 'positional'] + [f'given {n} {values[n]}' for n in names]
    calls = 0
    for name in 'ABC':
        if name in values:
            continue
        calls += 1
        values[name] = base + x if name == 'A' else values[chr(ord(name)-1)] + (delta if name == 'B' else extra)
        lines.append(f'default {name} {values[name]}')
    lines += [f'body {x} {values["A"]} {values["B"]} {values["C"]}', f'created {calls}', f'result {sum(values.values())} {calls}']
elif mode == 1:
    given = rng.choice([True, False])
    comparable = rng.choice([True, False])
    bound = 'subtype(comparable)' if comparable else 'type'
    check = 'if(Seed=Seed)then E else E' if comparable else 'E'
    args = ',?Extra:=block{Print("given");Z}' if given else ''
    recv = 'both(a,b)' if control else 'sink(v)'
    params = f'a:type,b:{bound}' if control else 'v:type'
    argty = '[]b' if control else 'v'
    ret = '[]b' if control else 'v'
    print(f'''leading(a:type) := interface {{ Tag():a }}
sink(v:type) := interface {{ Get(Z:v,?Extra:v)<suspends>:v }}
both(a:type,b:{bound}) := class(leading(a),sink([]b)):
    TagValue:a
    Seed:b
    Tag<override>():a=TagValue
    Get<override>(Z:[]b,?Extra:[]b=block{{Print("default");E:[]b=Concatenate();{check}}})<suspends>:[]b=
        Print("body")
        Sleep(0.001)
        Z+Extra+array{{Seed}}
Start(P:{recv},Z:{argty} where {params}){suspends}:task({ret})=spawn{{P.Get(Z{args})}}
Main()<suspends>:void=
    T:=Start(both(int,{ty}){{TagValue:=7,Seed:={value}}},array{{{value}}})
    Print("created")
    R:=T.Await()
    Print("length {{R.Length}}")''')
    lines = ['given' if given else 'default', 'body', 'created', f'length {3 if given else 2}']
else:
    selected = rng.choice(['child', 'other'])
    n = rng.randrange(1, 10)
    supplied = rng.choice([True, False])
    actual = rng.randrange(10, 30) if supplied else n
    named = f'?N:=Note({actual})' if supplied else ''
    recv = f'{selected}(u)' if control else 'out(v)'
    params = 'u:type' if control else 'v:type'
    ret = 'dog(u)' if control else 'v'
    print(f'''Note(N:int):int=block{{Print("given {{N}}");N}}
animal(t:type) := class {{ Value:t }}
dog(t:type) := class(animal(t)) {{ Woof():int=1 }}
carrier(t:type) := class:
    Value:t
    Seed:int={n}
    var Calls:int=0
    Get(?N:int=block{{set Calls+=1;Print("default {{Seed}}");Seed}})<suspends><computes>:t=
        Print("body {{N}}")
        Sleep(0.001)
        Value
out(v:type) := interface {{ Get(?N:int=0)<suspends><computes>:v }}
child(u:type) := class(carrier(dog(u)),out(animal(u))) {{}}
other(u:type) := class(carrier(dog(u)),out(animal(u))) {{ Pad:int=9 }}
Start(P:{recv} where {params}){suspends}:task({ret})=spawn{{P.Get({named})}}
Main()<suspends>:void=
    C:={selected}({ty}){{Value:=dog({ty}){{Value:={value}}}}}
    T:=Start(C)
    Print("created {{C.Calls}}")
    R:=T.Await()
    Print("value {{R.Value}} {{C.Calls}}")''')
    calls = int(not supplied)
    lines = [f'given {actual}' if supplied else f'default {n}', f'body {actual}', f'created {calls}', f'value {value.strip(chr(34))} {calls}']

Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
