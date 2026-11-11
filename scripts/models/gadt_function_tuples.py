#!/usr/bin/env python3
"""Tuple adapters preserve ordered arguments, values, effects and bounds.

The oracle models tuple construction/projection, counters and rollback rather
than compiler representation. --control emits ordinary direct generic calls.
"""
import random
import sys
from pathlib import Path

rng = random.Random(int(sys.argv[1]))
control = '--control' in sys.argv[3:]
mode = rng.randrange(6)
ty, v, w = rng.choice([('int', str(rng.randrange(1, 8)), str(rng.randrange(10, 18))),
                       ('string', '"old"', '"new"')])
other, x = rng.choice([('int', str(rng.randrange(20, 30))), ('string', '"input"')])
shown = lambda s: s.strip('"')
n = rng.randrange(2, 9)
lines = []
print('cell:=class{var N:int=0}')

if mode == 0:
    bind = 'P:=Packet(C,X,Y)' if control else 'F:type{_(:tuple(cell,t,u)):tuple(u,t)}=Swap'
    call = 'Swap(P(0),P(1),P(2))' if control else 'F(Packet(C,X,Y))'
    print(f'''Packet(C:cell,X:t,Y:u where t:type,u:type):tuple(cell,t,u)=
    set C.N+=1
    Print("packet {{C.N}}")
    (C,X,Y)
Swap(C:cell,X:t,Y:u where t:type,u:type):tuple(u,t)=
    set C.N+=1
    Print("swap {{C.N}}")
    (Y,X)
Run(C:cell,X:t,Y:u where t:type,u:type):tuple(u,t)=
    {bind}
    {call}
Main():void=
    C:=cell{{}}
    R:=Run(C,{v},{x})
    Print("result {{R(0)}} {{R(1)}} state {{C.N}}")''')
    lines = ['packet 1', 'swap 2', f'result {shown(x)} {shown(v)} state 2']
elif mode == 1:
    bind = '' if control else 'F:type{_(:cell,:t,:u,:t):tuple(t,u,t)}=Flip\n    '
    call = 'Flip((Touch(C),X,Y,Z))' if control else 'F(Touch(C),X,Y,Z)'
    print(f'''Touch(C:cell):cell=
    set C.N+=1
    Print("argument {{C.N}}")
    C
Flip(P:tuple(cell,t,u,t) where t:type,u:type):tuple(t,u,t)=
    C:=P(0)
    set C.N+=1
    Print("flip {{C.N}}")
    (P(3),P(2),P(1))
Run(C:cell,X:t,Y:u,Z:t where t:type,u:type):tuple(t,u,t)=
    {bind}{call}
Main():void=
    C:=cell{{}}
    R:=Run(C,{v},{x},{w})
    Print("result {{R(0)}} {{R(1)}} {{R(2)}} state {{C.N}}")''')
    lines = ['argument 1', 'flip 2', f'result {shown(w)} {shown(x)} {shown(v)} state 2']
elif mode == 2:
    triple = rng.choice([True, False])
    types = 't,u,t' if triple else 't,u'
    vals = 'X,Y,Z' if triple else 'X,Y'
    ps = ':t,:u,:t' if triple else ':t,:u'
    bind = '' if control else f'F:type{{_({ps})<computes>:tuple({types})}}=Id\n    '
    call = f'Id(({vals}))' if control else f'F({vals})'
    main_args = f'{v},{x},{w}' if triple else f'{v},{x}'
    third = ' {R(2)}' if triple else ''
    print(f'''Id(X:t where t:subtype(comparable))<computes>:t=X
Run(X:t,Y:u{',Z:t' if triple else ''} where t:subtype(comparable),u:subtype(comparable))<computes>:tuple({types})=
    {bind}{call}
Main():void=
    R:=Run({main_args})
    Print("result {{R(0)}} {{R(1)}}{third}")''')
    lines = [f'result {shown(v)} {shown(x)}' + (f' {shown(w)}' if triple else '')]
elif mode == 3:
    bind = '' if control else 'F:type{_(:cell,:t,:t)<transacts><decides>:t}=Match\n    '
    call = lambda a: f'Match[(C,{a},X)]' if control else f'F[C,{a},X]'
    print(f'''Match(P:tuple(cell,t,t) where t:subtype(comparable))<transacts><decides>:t=
    C:=P(0)
    set C.N+=1
    Print("try {{C.N}}")
    P(1)=P(2)
    P(1)
Run(C:cell,X:t,Y:t where t:subtype(comparable))<transacts>:void=
    {bind}if({call('Y')})then Print("wrong")else Print("miss {{C.N}}")
    if({call('X')},Print("suffix"),false?)then Print("wrong")else Print("reject {{C.N}}")
    if({call('X')})then Print("hit {{C.N}}")else Print("wrong")
Main():void=Run(cell{{}},{v},{w})''')
    lines = ['miss 0', 'reject 0', 'try 1', 'hit 1']
elif mode == 4:
    pack = rng.choice([True, False])
    header = 'C:cell,X:t,Y:u' if pack else 'P:tuple(cell,t,u)'
    unpack = '' if pack else 'C:=P(0)\n    X:=P(1)\n    Y:=P(2)\n    '
    fparams = ':tuple(cell,t,u)' if pack else ':cell,:t,:u'
    args = '(C,X,Y)' if pack else 'C,X,Y'
    direct = 'Later(C,X,Y)' if pack else 'Later((C,X,Y))'
    factory = '' if control else f'Bind(X:t,Y:u where t:type,u:type):type{{_({fparams})<suspends>:tuple(t,u)}}=Later\n'
    bind = '' if control else 'F:=Bind(X,Y)\n    '
    call = direct if control else f'F({args})'
    print(f'''Later({header} where t:type,u:type)<suspends>:tuple(t,u)=
    {unpack}set C.N+=1
    Print("begin {{C.N}}")
    defer: Print("cleanup {{C.N}}")
    Sleep(1.0)
    Print("end {{C.N}}")
    (X,Y)
{factory}Run(C:cell,X:t,Y:u where t:type,u:type)<suspends>:void=
    {bind}T:=spawn{{{call}}}
    R:=T.Await()
    Print("done {{C.N}}")
    race:
        {call}
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished")
Main()<suspends>:void=Run(cell{{}},{v},{x})''')
    lines = ['begin 1', 'end 1', 'cleanup 1', 'done 1', 'begin 2', 'cancel', 'cleanup 2', 'finished']
else:
    factory = '' if control else 'Bind(X:t,Y:u where t:subtype(comparable),u:subtype(comparable))<computes>:type{_(:t,:u)<computes>:tuple(t,u)}=Id\n'
    bind = '' if control else 'F:=Bind(D.V,D.Other)\n        '
    call = 'Id((D.V,D.Other))' if control else 'F(D.V,D.Other)'
    print(f'''Id(X:t where t:subtype(comparable))<computes>:t=X
{factory}root(t:type):=class{{V:t;N:int}}
extra(a:subtype(comparable),b:subtype(comparable)):=class(root(a)){{Other:b}}
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        {bind}R:={call}
        if(R(0)=D.V,R(1)=D.Other)then Print("opened {{D.N}}")else Print("wrong")
    else:
        Print("base {{P.N}}")
Main():void=
    Use(extra({ty},{other}){{V:={v},Other:={x},N:={n}}})
    Use(extra({other},{ty}){{V:={x},Other:={w},N:={n+1}}})
    Use(root(int){{V:=3,N:={n+2}}})''')
    lines = [f'opened {n}', f'opened {n+1}', f'base {n+2}']

Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
