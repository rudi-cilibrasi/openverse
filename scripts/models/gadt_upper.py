#!/usr/bin/env python3
"""Upper bounds on a GADT's type parameter (#502, #209), modeled from
LANGUAGE.md ("Parametric functions", "Type constraints"), independently of
the front end's code.

    usage: gadt_upper.py SEED EXPECTED > PROGRAM

A root class expr(t:subtype(shape)) holds a t; lit_sq fixes t to sq. Generic
functions bounded by shape read members through the bound (dispatching to
the precise class's override), return the precise t, take several values,
refine t with a cast to lit_sq, relate a peer u:subtype(t), and take a
castable_subtype(shape) bound. The model predicts each line; one program in
six instead writes an instance the bound refuses, and expects that message.
fuzz-model-gadt.sh runs it on a random stream of its own, so the other
models keep their seeds.
"""
import random
import sys
from pathlib import Path

seed = int(sys.argv[1])
rng = random.Random(seed * 1000003 + 502)

source = '''shape:=class<computes><castable>:
    Tag:int=0
    Area()<computes>:int=0
sq:=class<computes>(shape):
    Side:int=1
    Area<override>()<computes>:int=Side*Side
rect:=class<computes>(shape):
    W:int=1
    H:int=1
    Area<override>()<computes>:int=W*H
expr(t:subtype(shape)):=class<computes>:
    Value:t
    Area()<computes>:int=Value.Area()
lit_sq:=class<computes>(expr(sq)):
    Extra:int=0
Eval(E:expr(t) where t:subtype(shape))<computes>:t=E.Value
Measure(E:expr(t) where t:subtype(shape))<computes>:int=
    if(L:=lit_sq[E]) then L.Value.Side*100+L.Extra else E.Area()
Both(X:expr(t),Y:expr(t) where t:subtype(shape))<computes>:t=X.Value|Y.Value
Wider(E:expr(t),F:u,Pick:logic where t:subtype(shape),u:subtype(t))<computes>:t=if(Pick?) then F else E.Value
Keep(X:t where t:castable_subtype(shape))<computes>:t=X
'''

if rng.randrange(6) == 0:
    # an instance the bound refuses, in one of the places a bound is checked
    bad = rng.choice(['    X:=expr(int){Value:=3}\n',
                      '    X:=Eval(expr(int){Value:=3})\n',
                      '    X:=Keep(3)\n'])
    source += 'Main():void=\n' + bad
    expected = 'exit=4\ndoes not satisfy subtype(shape)\n'
    print(source, end='')
    Path(sys.argv[2]).write_text(expected)
    sys.exit(0)

# The model's values: ('rect', W, H), ('sq', Side) and ('lit', Side, Extra).
def area(e):
    return e[1] * e[2] if e[0] == 'rect' else e[1] * e[1]

exprs = []
main = []
lines = []
for i in range(rng.randint(2, 5)):
    kind = rng.choice(['rect', 'sq', 'lit'])
    name = f'E{i}'
    if kind == 'rect':
        e = ('rect', rng.randint(1, 6), rng.randint(1, 6))
        main.append(f'{name}:=expr(rect){{Value:=rect{{W:={e[1]},H:={e[2]}}}}}')
    elif kind == 'sq':
        e = ('sq', rng.randint(1, 6))
        main.append(f'{name}:=expr(sq){{Value:=sq{{Side:={e[1]}}}}}')
    else:
        e = ('lit', rng.randint(1, 6), rng.randint(0, 9))
        main.append(f'{name}:expr(sq)=lit_sq{{Value:=sq{{Side:={e[1]}}},Extra:={e[2]}}}')
    exprs.append((name, e))

for _ in range(rng.randint(3, 7)):
    k = rng.choice(['eval', 'measure', 'area', 'both', 'first', 'wider', 'keep'])
    name, e = rng.choice(exprs)
    if k == 'eval':
        # the precise class's own member, through the bound's result
        if e[0] == 'rect':
            main.append(f'Print("eval {{Eval({name}).W}} {{Eval({name}).H}}")')
            lines.append(f'eval {e[1]} {e[2]}')
        else:
            main.append(f'Print("eval {{Eval({name}).Side}}")')
            lines.append(f'eval {e[1]}')
    elif k == 'measure':
        main.append(f'Print("measure {{Measure({name})}}")')
        lines.append(f'measure {e[1] * 100 + e[2] if e[0] == "lit" else area(e)}')
    elif k == 'area':
        main.append(f'Print("area {{{name}.Area()}} {{Eval({name}).Area()}}")')
        lines.append(f'area {area(e)} {area(e)}')
    elif k in ('both', 'first'):
        same = [(n, x) for (n, x) in exprs if (x[0] == 'rect') == (e[0] == 'rect')]
        other, f = rng.choice(same)
        member = 'W' if e[0] == 'rect' else 'Side'
        val = lambda x: x[1]
        if k == 'both':
            main.append(f'for(V:=Both({name},{other})){{Print("both {{V.{member}}} {{V.Area()}}")}}')
            lines += [f'both {val(e)} {area(e)}', f'both {val(f)} {area(f)}']
        else:
            limit = rng.randint(0, 6)
            main.append(f'if(V:=Both({name},{other}),V.{member}>{limit}) then Print("first {{V.{member}}}") else Print("none")')
            got = [x for x in (e, f) if val(x) > limit]
            lines.append(f'first {val(got[0])}' if got else 'none')
    elif k == 'wider':
        # a peer u below t: a lit_sq's sq, or a fresh one of t's class
        pick = rng.choice(['true', 'false'])
        if e[0] == 'rect':
            w, h = rng.randint(1, 6), rng.randint(1, 6)
            main.append(f'Print("wider {{Wider({name},rect{{W:={w},H:={h}}},{pick}).Area()}}")')
            lines.append(f'wider {w * h if pick == "true" else area(e)}')
        else:
            s = rng.randint(1, 6)
            main.append(f'Print("wider {{Wider({name},sq{{Side:={s}}},{pick}).Side}}")')
            lines.append(f'wider {s if pick == "true" else e[1]}')
    else:
        s = rng.randint(1, 6)
        main.append(f'Print("keep {{Keep(sq{{Side:={s}}}).Side}} {{Keep({name}.Value).Area()}}")')
        lines.append(f'keep {s} {area(e)}')

source += 'Main():void=\n' + ''.join(f'    {l}\n' for l in main)
print(source, end='')
Path(sys.argv[2]).write_text('exit=0\n' + ''.join(l + '\n' for l in lines))
