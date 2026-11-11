#!/usr/bin/env python3
"""Bound tuple-adapted methods agree with ordinary receiver calls.

A state/order/rollback/cleanup oracle, with --control for pre-change calls.
"""
import random
import sys
from pathlib import Path

rng = random.Random(int(sys.argv[1]))
control = '--control' in sys.argv[3:]
mode = rng.randrange(6)
ty, v, w = rng.choice([('int', str(rng.randrange(1, 8)), str(rng.randrange(10, 18))),
                       ('string', '"old"', '"new"')])
other, y = rng.choice([('int', str(rng.randrange(20, 30))), ('string', '"input"')])
shown = lambda s: s.strip('"')
n = rng.randrange(2, 8)
print('cell:=class{var N:int=0}')

if mode == 0:
    bind = 'Receiver:=Touch(B)' if control else 'F:type{_(:tuple(a,b)):tuple(u,a,b)}=Touch(B).Pair'
    call = 'Receiver.Pair(P(0),P(1))' if control else 'F(P)'
    print(f'''box(t:type):=class:
    var V:t
    C:cell
    Pair(X:a,Y:b where a:type,b:type):tuple(t,a,b)=
        set C.N+=1
        Print("pair {{C.N}}")
        (V,X,Y)
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {{B.C.N}}")
    B
Packet(C:cell,X:a,Y:b where a:type,b:type):tuple(a,b)=
    set C.N+=1
    Print("packet {{C.N}}")
    (X,Y)
Run(B:box(u),X:a,Y:b,Next:u where u:type,a:type,b:type):tuple(u,a,b)=
    {bind}
    set B.V=Next
    P:=Packet(B.C,X,Y)
    {call}
Main():void=
    R:=Run(box({ty}){{V:={v},C:=cell{{}}}},{v},{y},{w})
    Print("result {{R(0)}} {{R(1)}} {{R(2)}}")''')
    lines = ['receiver 1', 'packet 2', 'pair 3', f'result {shown(w)} {shown(v)} {shown(y)}']
elif mode == 1:
    bind = '' if control else 'F:type{_(:u,:u)<transacts><decides>:u}=B.Match\n    '
    call = lambda a: f'B.Match[({a},X)]' if control else f'F[{a},X]'
    print(f'''box(t:type):=class:
    V:t
    C:cell
    Match(P:tuple(a,a) where a:subtype(comparable))<transacts><decides>:a=
        set C.N+=1
        Print("try {{C.N}}")
        P(0)=P(1)
        P(0)
Run(B:box(t),X:u,Y:u where t:type,u:subtype(comparable))<transacts>:void=
    {bind}if({call('Y')})then Print("wrong")else Print("miss {{B.C.N}}")
    if({call('X')},Print("suffix"),false?)then Print("wrong")else Print("reject {{B.C.N}}")
    if({call('X')})then Print("hit {{B.C.N}}")else Print("wrong")
Main():void=Run(box(int){{V:={n},C:=cell{{}}}},{v},{w})''')
    lines = ['miss 0', 'reject 0', 'try 1', 'hit 1']
elif mode == 2:
    factory = '' if control else 'Bind(B:box(tuple(a,b),c) where a:type,b:type,c:type):type{_(:a,:b):tuple(a,b)}=B.Echo\n'
    bind = '' if control else 'F:=Bind(B)\n    '
    call = 'B.Echo((X,Y))' if control else 'F(X,Y)'
    print(f'''box(t:type,h:type):=class:
    Hidden:h
    C:cell
    Echo(X:t):t=
        set C.N+=1
        Print("echo {{C.N}}")
        X
{factory}Run(B:box(tuple(a,b),c),X:a,Y:b where a:type,b:type,c:type):tuple(a,b)=
    {bind}set B.C.N+={n}
    {call}
Main():void=
    R:=Run(box(tuple({ty},{other}),string){{Hidden:="hidden",C:=cell{{}}}},{v},{y})
    Print("result {{R(0)}} {{R(1)}}")''')
    lines = [f'echo {n+1}', f'result {shown(v)} {shown(y)}']
elif mode == 3:
    factory = '' if control else 'Bind(B:source(c),X:a,Y:b where c:type,a:subtype(comparable),b:subtype(comparable)):type{_(:a,:b):tuple(a,b)}=B.Id\n'
    bind = '' if control else 'F:=Bind(D,D.V,D.Other)\n        '
    call = 'D.Id((D.V,D.Other))' if control else 'F(D.V,D.Other)'
    print(f'''source(t:type):=interface:
    Get():t
    Id(X:u where u:subtype(comparable)):u=X
root(t:type):=class(source(t)):
    V:t
    N:int
    Get<override>():t=V
extra(a:subtype(comparable),b:subtype(comparable)):=class(root(a)){{Other:b}}
{factory}Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        {bind}R:={call}
        if(R(0)=D.V,R(1)=D.Other)then Print("opened {{D.N}}")else Print("wrong")
    else:
        Print("base {{P.N}}")
Main():void=
    Use(extra({ty},{other}){{V:={v},Other:={y},N:={n}}})
    Use(extra({other},{ty}){{V:={y},Other:={w},N:={n+1}}})
    Use(root(int){{V:=3,N:={n+2}}})''')
    lines = [f'opened {n}', f'opened {n+1}', f'base {n+2}']
elif mode == 4:
    pack = rng.choice([True, False])
    header = 'X:a,Y:b' if pack else 'P:tuple(a,b)'
    result = '(X,Y)' if pack else 'P'
    fparams = ':tuple(a,b)' if pack else ':a,:b'
    args = '(X,Y)' if pack else 'X,Y'
    direct = 'Receiver.Later(X,Y)' if pack else 'Receiver.Later((X,Y))'
    bind = 'Receiver:=Touch(B)' if control else f'F:type{{_({fparams})<suspends>:tuple(a,b)}}=Touch(B).Later'
    call = direct if control else f'F({args})'
    print(f'''box(t:type):=class:
    V:t
    C:cell
    Later({header} where a:type,b:type)<suspends>:tuple(a,b)=
        set C.N+=1
        Print("begin {{C.N}}")
        defer: Print("cleanup {{C.N}}")
        Sleep(1.0)
        Print("end {{C.N}}")
        {result}
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {{B.C.N}}")
    B
Run(B:box(t),X:a,Y:b where t:type,a:type,b:type)<suspends>:void=
    {bind}
    T:=spawn{{{call}}}
    R:=T.Await()
    Print("done {{B.C.N}}")
    race:
        {call}
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished")
Main()<suspends>:void=Run(box(int){{V:={n},C:=cell{{}}}},{v},{y})''')
    lines = ['receiver 1', 'begin 2', 'end 2', 'cleanup 2', 'done 2', 'begin 3', 'cancel', 'cleanup 3', 'finished']
else:
    bind = '' if control else '''F:type{_():t}=B.Empty
    G:type{_(:tuple()):t}=B.Get
    H:type{_(:tuple(u)):u}=B.Id
    I:type{_(:u):tuple(u)}=B.Id
    '''
    calls = 'B.Empty(()),B.Get(),B.Id(X),B.Id(X)' if control else 'F(),G(()),H(I(X)),I(X)(0)'
    print(f'''box(t:type,h:type):=class:
    V:t
    Hidden:h
    Empty(P:tuple()):t=V
    Get():t=V
    Id(X:u where u:type):u=X
Run(B:box(t,h),X:u where t:type,h:type,u:type):tuple(t,t,u,u)=
    {bind}({calls})
Main():void=
    R:=Run(box({ty},string){{V:={v},Hidden:="hidden"}},{y})
    Print("result {{R(0)}} {{R(1)}} {{R(2)}} {{R(3)}}")''')
    lines = [f'result {shown(v)} {shown(v)} {shown(y)} {shown(y)}']

Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
