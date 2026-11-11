#!/usr/bin/env python3
"""Covariant multi-value dispatch model (#283), from LANGUAGE.md.

The dynamic class selects an implementation and its defaults. The receiver's
static declaration selects the promised result type. A real choice introduces
a generator boundary; a scalar override does not. Rejected first-success
searches roll back all their effects. Predict object identity/order, field
values, call evaluation order and filter rollback without compiler helpers.
"""
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
case = seed // 7
rng = random.Random(seed)
iface = bool((case // 7) % 2)
leaf = rng.choice(['int', 'string'])
kinds = ['factory', 'kennel', 'pups', 'quiet', 'extra', 'ints', 'inherited']
kind = kinds[case % len(kinds)]
if kind == 'ints':
    leaf = 'int'
minimum = rng.randint(0, 10)
explicit = bool(rng.randrange(2))
a, b = rng.sample(range(1, 10), 2)

# The model's method table is distinct from the emitted source declarations.
implementation = {'inherited': 'kennel'}.get(kind, kind)
results = {
    'factory': ['a', 'b'], 'kennel': ['b', 'a'], 'pups': ['b', 'b'],
    'quiet': ['a'], 'extra': ['a', 'a', 'b'], 'ints': ['a', 'b'],
}[implementation]
objects = {'a': {'n': a, 'code': 10 + a}, 'b': {'n': b, 'code': 20 + b}}
for o in objects.values():
    o['value'] = str(o['n']) if leaf == 'int' else 'v' + str(o['n'])
# A selected scalar implementation has no generator at which to keep the prefix.
generator = len(results) > 1
prefix = 'ra' + ('n' if explicit else 'd' + implementation) + 'p' + implementation
accepted = [name for name in results if objects[name]['n'] >= minimum]
all_log = prefix if generator else (prefix if accepted else '')
all_log += 'b' * len(accepted)
first_log = prefix if accepted else ''

source = '''counter := class { var Log:string = "" }
Mark(C:counter,S:string)<transacts>:int =
    set C.Log = "{C.Log}{S}"
    0
item(t:type) := class { V:t; N:int }
dog(t:type) := class(item(t)) { Code:int }
pup(t:type) := class(dog(t)) { Extra:int = 99 }
'''
root = 'maker' if iface else 'factory'
if iface:
    source += '''maker(t:type) := interface:
    Get(C:counter,X:int,?Q:int=Mark(C,"dmaker"))<transacts>:item(t)
'''
source += f'''factory(t:type) := class{'(maker(t))' if iface else ''}:
    A:dog(t)
    B:pup(t)
    Get{'<override>' if iface else ''}(C:counter,X:int,?Q:int=Mark(C,"dfactory"))<transacts>:item(t) =
        Mark(C,"pfactory")
        A | B
kennel(t:type) := class(factory(t)):
    Get<override>(C:counter,X:int,?Q:int=Mark(C,"dkennel"))<transacts>:dog(t) =
        Mark(C,"pkennel")
        B | A
pups(t:type) := class(kennel(t)):
    Get<override>(C:counter,X:int,?Q:int=Mark(C,"dpups"))<transacts>:pup(t) =
        Mark(C,"ppups")
        B | B
quiet(t:type) := class(kennel(t)):
    Get<override>(C:counter,X:int,?Q:int=Mark(C,"dquiet"))<transacts>:dog(t) =
        Mark(C,"pquiet")
        A
extra(t:type,u:subtype(comparable)) := class(kennel(t)):
    E:u
    Get<override>(C:counter,X:int,?Q:int=block{{W:[]u=Concatenate(); Z:[]t=Concatenate(); Mark(C,"dextra")}})<transacts>:dog(t) =
        Mark(C,"pextra")
        A | A | B
ints := class(kennel(int)):
    Get<override>(C:counter,X:int,?Q:int=Mark(C,"dints"))<transacts>:dog(int) =
        Mark(C,"pints")
        A | B
inherited(t:type) := class(kennel(t)) {{}}
Receive(P:{root}(t),C:counter where t:type)<transacts>:{root}(t) =
    Mark(C,"r")
    P
ReceiveDog(P:kennel(t),C:counter where t:type)<transacts>:kennel(t) =
    Mark(C,"r")
    P
'''
passed = ',?Q:=Mark(C,"n")' if explicit else ''
source += f'''All(P:{root}(t),C:counter,Min:int where t:type)<transacts>:[]item(t) =
    for(D:=Receive(P,C).Get(C,Mark(C,"a"){passed}),D.N>=Min):
        Mark(C,"b")
        D
FirstDog(P:kennel(t),C:counter,Min:int where t:type)<transacts>:int =
    if(D:=ReceiveDog(P,C).Get(C,Mark(C,"a"){passed}),D.N>=Min) then D.Code else -1
TakeDogs(P:kennel(t),C:counter where t:type)<transacts>:[]dog(t) = for(D:=P.Get(C,0)){{D}}
'''

mode = case % 9
if mode == 8:
    source += f'''Bad(P:{root}(t) where t:type)<transacts>:int =
    D:=P.Get(counter{{}},0)
    D.Code
Main():void = Print("unused")
'''
    expected = 'exit=4\nhas no field\n'
else:
    def literal(n):
        return str(n) if leaf == 'int' else f'"v{n}"'
    own = kind if kind == 'ints' else kind + '(' + leaf + (',string' if kind == 'extra' else '') + ')'
    ef = ',E:="hidden"' if kind == 'extra' else ''
    show = '"{D.V}"' if leaf == 'int' else 'D.V'
    source += f'''Main()<transacts>:void =
    A:=dog({leaf}){{V:={literal(a)},N:={a},Code:={10+a}}}
    B:=pup({leaf}){{V:={literal(b)},N:={b},Code:={20+b}}}
    P:={own}{{A:=A,B:=B{ef}}}
    C:=counter{{}}
    R:=All(P,C,{minimum})
    for(D:R){{Print({show})}}
    Print("all {{C.Log}}")
'''
    lines = [objects[x]['value'] for x in accepted] + ['all ' + all_log]
    if kind != 'factory':
        source += f'''    set C.Log = ""
    Print("first {{FirstDog(P,C,{minimum})}} {{C.Log}}")
    set C.Log = ""
    for(D:TakeDogs(P,C)){{Print("dog {{D.Code}}")}}
    Print("dogs {{C.Log}}")
'''
        lines += [f"first {objects[accepted[0]]['code'] if accepted else -1} {first_log}"]
        lines += [f"dog {objects[x]['code']}" for x in results]
        lines += ['dogs d' + implementation + 'p' + implementation]
        # The direct call uses the concrete receiver's narrower declaration,
        # rather than inferring a wide type from the dynamic alternatives.
        source += f'''    set C.Log = ""
    for(D:=P.Get(C,0)){{Print("direct {{D.Code}}")}}
'''
        lines += [f"direct {objects[x]['code']}" for x in results]
    expected = 'exit=0\n' + '\n'.join(lines) + '\n'

print(source, end='')
Path(sys.argv[2]).write_text(expected)
