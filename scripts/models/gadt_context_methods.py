#!/usr/bin/env python3
"""Contextual bound methods agree with explicit typed receiver captures.

Models runtime order, rollback, defaults, opened bounds and cancellation.
--control emits explicitly bound instances for the preceding compiler.
"""
import random
import sys
from pathlib import Path

rng = random.Random(int(sys.argv[1]))
control = '--control' in sys.argv[3:]
mode = rng.randrange(6)
ty, value = rng.choice([('int', str(rng.randrange(2, 12))), ('string', '"input"')])
n = rng.randrange(2, 7)
print('cell:=class{var N:int=0}')
print('''Tick(C:cell,Tag:string):int=
    set C.N+=1
    Print("{Tag} {C.N}")
    C.N
Arg(C:cell,X:t where t:type):t=
    N:=Tick(C,"arg")
    X''')

if mode in (0, 1):
    bind = 'F:type{_(:u):u}=Touch(B).Same\n    ' if control else ''
    f = 'F' if control else 'Touch(B).Same'
    if mode == 0:
        body = f'{bind}Apply({f},Arg(B.C,X))'
        output = f'''R:=Run(box(int){{V:={n},C:=cell{{}}}},{value})
    Print("result {{R}}")'''
        lines = ['receiver 1', 'arg 2', 'same 3', 'result 1']
    else:
        # A wrapper keeps the explicit capture inside each trial's filter.
        wrapper = f'''Call(B:box(t),X:u where t:type,u:type):u=
    {bind}Twice({f},Arg(B.C,X))'''
        body = '''if(V:=Call(B,X),false?)then Print("wrong")else Print("miss {B.C.N}")
    R:=for(V:=Call(B,X)):Print("value {B.C.N}")
    R.Length'''
        output = f'''C:=cell{{}}
    R:=Run(box(int){{V:={n},C:=C}},{value})
    Print("result {{R}} {{C.N}}")'''
        lines = ['miss 0', 'receiver 1', 'arg 2', 'same 3', 'value 3', 'same 4', 'value 4', 'result 2 4']
    print(f'''box(t:type):=class:
    V:t
    C:cell
    Same(X:u where u:type):u=
        N:=Tick(C,"same")
        X
Touch(B:box(t) where t:type):box(t)=
    N:=Tick(B.C,"receiver")
    B
Apply(F:type{{_(:t):t}},X:t where t:subtype(comparable)):int=if(F(X)=X)then 1 else -1
Twice(F:type{{_(:t):t}},X:t where t:type):t=F(X)|F(X)
{wrapper if mode == 1 else ''}
Run(B:box(t),X:u where t:type,u:subtype(comparable)):int=
    {body}
Main():void=
    {output}''')
elif mode == 2:
    bind = 'Owner:=TouchA(A)\n    F:type{_(:u):u}=TouchB(B).Same\n    ' if control else ''
    owner = 'Owner' if control else 'TouchA(A)'
    f = 'F' if control else 'TouchB(B).Same'
    print(f'''box:=class:
    C:cell
    Same(X:t where t:type):t=
        N:=Tick(C,"same")
        X
applicator(t:type):=class:
    V:t
    C:cell
    Apply(F:type{{_(:u):u}},?X:u,?N:int=Tick(C,"default") where u:subtype(comparable)):int=if(F(X)=X)then 1 else -1
TouchA(A:applicator(t) where t:type):applicator(t)=
    N:=Tick(A.C,"owner")
    A
TouchB(B:box):box=
    N:=Tick(B.C,"receiver")
    B
Run(A:applicator(t),B:box,X:u where t:type,u:subtype(comparable)):int=
    {bind}{owner}.Apply({f},?X:=Arg(B.C,X))
Main():void=
    C:=cell{{}}
    R:=Run(applicator(int){{V:={n},C:=C}},box{{C:=C}},{value})
    Print("result {{R}} {{C.N}}")''')
    lines = ['owner 1', 'receiver 2', 'arg 3', 'default 4', 'same 5', 'result 1 5']
elif mode == 3:
    bind = 'F:=Bind(Touch(D),D.V,D.Other)\n        ' if control else ''
    f = 'F' if control else 'Touch(D).Id'
    print(f'''root(t:type):=class:
    V:t
    C:cell
    N:int
    Id(X:u where u:subtype(comparable))<computes>:u=X
extra(a:subtype(comparable),b:subtype(comparable)):=class(root(a)){{Other:b}}
Touch(B:root(t) where t:type):root(t)=
    N:=Tick(B.C,"receiver")
    B
Bind(B:root(t),X:a,Y:b where t:type,a:subtype(comparable),b:subtype(comparable))<computes>:type{{_(:a,:b)<computes>:tuple(a,b)}}=B.Id
Twice(F:type{{_(:a,:b)<computes>:tuple(a,b)}},X:a,Y:b where a:subtype(comparable),b:subtype(comparable))<computes>:tuple(a,b)=F(X,Y)|F(X,Y)
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        {bind}R:=for(V:=Twice({f},D.V,D.Other)):
            if(V(0)=D.V,V(1)=D.Other)then 1 else 0
        Print("opened {{D.N}} {{R.Length}}")
    else:
        Print("base {{P.N}}")
Main():void=
    Use(extra({ty},int){{V:={value},Other:=3,C:=cell{{}},N:={n}}})
    Use(root(int){{V:=7,C:=cell{{}},N:={n+1}}})''')
    lines = ['receiver 1', f'opened {n} 2', f'base {n+1}']
elif mode == 4:
    bind = 'F:type{_(:u)<suspends>:u}=Touch(B).Later\n    ' if control else ''
    f = 'F' if control else 'Touch(B).Later'
    print(f'''box:=class:
    C:cell
    Later(X:u where u:type)<suspends>:u=
        N:=Tick(C,"begin")
        defer: Print("cleanup {{C.N}}")
        Sleep(1.0)
        Print("end {{C.N}}")
        X
Touch(B:box):box=
    N:=Tick(B.C,"receiver")
    B
Apply(F:type{{_(:u)<suspends>:u}},X:u where u:subtype(comparable))<suspends>:int=
    R:=F(X)
    if(R=X)then 1 else -1
Call(B:box,X:u where u:subtype(comparable))<suspends>:int=
    {bind}Apply({f},Arg(B.C,X))
Run(B:box,X:t where t:subtype(comparable))<suspends>:void=
    T:=spawn{{Call(B,X)}}
    R:=T.Await()
    Print("done {{R}} {{B.C.N}}")
    race:
        Call(B,X)
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished")
Main()<suspends>:void=Run(box{{C:=cell{{}}}},{value})''')
    lines = ['receiver 1', 'arg 2', 'begin 3', 'end 3', 'cleanup 3', 'done 1 3', 'receiver 4', 'arg 5', 'begin 6', 'cancel', 'cleanup 6', 'finished']
else:
    print('''Id(X:t where t:type)<computes>:t=X
UseGlobal():int=block{F:type{_(:int)<computes>:int}=Id;F(1)}
Show(X:int)<computes>:string="show {X}"
Map(F:type{_(:int)<computes>:u},X:int where u:type)<computes>:u=F(X)
reader:=class:
    Id:type{_(:int)<computes>:string}=Show
    Read():string=Map(Id,6)
base:=class:
    Id(X:int)<computes>:string="method {X}"
child:=class(base):
    Id(X:string)<computes>:int=X.Length
Main():void=
    B:=reader{}
    R:=Map(B.Id,3)
    Print(R)
    Print(B.Read())
    A:=base{}
    S:=Map(A.Id,7)
    Print(S)''')
    lines = ['show 3', 'show 6', 'method 7']

Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
