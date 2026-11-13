#!/usr/bin/env python3
"""Contextual generic values agree with explicitly bound instances.

Models argument/default order, rollback, recursive sequences and lexical lookup.
--control binds generic identifiers before the call for the older compiler.
"""
import random
import sys
from pathlib import Path

rng = random.Random(int(sys.argv[1]))
control = '--control' in sys.argv[3:]
mode = rng.randrange(6)
ty, value = rng.choice([('int', str(rng.randrange(2, 12))), ('string', '"input"')])
n = rng.randrange(2, 6)
print('cell:=class{var N:int=0}')
print('Id(X:t where t:type)<computes>:t=X')
print('''Mark(C:cell,X:t where t:type):t=
    set C.N+=1
    Print("arg {C.N}")
    X''')

if mode in (0, 1):
    bind = 'F:type{_(:t)<computes>:t}=Id\n    ' if control else ''
    f = 'F' if control else 'Id'
    if mode == 0:
        body = f'''R:=for(V:=Twice({f},Mark(C,X))):
        set C.N+=1
        if(V=X)then Print("value {{C.N}}")else Print("wrong")
    R.Length'''
        lines = ['arg 1', 'value 2', 'value 3', 'result 2 state 3']
    else:
        body = f'''if(V:=Twice({f},Mark(C,X)),false?)then Print("wrong")else Print("miss {{C.N}}")
    if(V:=Twice({f},Mark(C,X)),V=X)then Print("hit {{C.N}}")else Print("wrong")
    C.N'''
        lines = ['miss 0', 'arg 1', 'hit 1', 'result 1 state 1']
    print(f'''Twice(F:type{{_(:t)<computes>:t}},X:t where t:subtype(comparable))<computes>:t=F(X)|F(X)
Run(C:cell,X:t where t:subtype(comparable)):int=
    {bind}{body}
Main():void=
    C:=cell{{}}
    R:=Run(C,{value})
    Print("result {{R}} state {{C.N}}")''')
elif mode == 2:
    bind = 'F:type{_(:t)<computes>:t}=Id\n    ' if control else ''
    f = 'F' if control else 'Id'
    print(f'''Default(C:cell):int=
    set C.N+=1
    Print("default {{C.N}}")
    C.N
Twice(C:cell,?F:type{{_(:t)<computes>:t}},?X:t,?N:int=Default(C) where t:subtype(comparable)):t=F(X)|F(X)
Run(C:cell,X:t where t:subtype(comparable)):int=
    {bind}R:=for(V:=Twice(C,?F:={f},?X:=Mark(C,X))):
        set C.N+=1
        if(V=X)then Print("value {{C.N}}")else Print("wrong")
    R.Length
Main():void=
    C:=cell{{}}
    R:=Run(C,{value})
    Print("result {{R}} state {{C.N}}")''')
    lines = ['arg 1', 'default 2', 'value 3', 'value 4', 'result 2 state 4']
elif mode == 3:
    bind = 'F:type{_(:t)<computes>:t}=Id\n    ' if control else ''
    f = 'F' if control else 'Id'
    print(f'''Levels(F:type{{_(:t)<computes>:t}},X:t,N:int where t:type)<computes>:int=
    Y:=F(X)
    if(N<1)then 0 else N|Levels(Id,Y,N-1)
Run(C:cell,X:t where t:type):int=
    {bind}R:=for(V:=Levels({f},Mark(C,X),{n})):Print("value {{V}}")
    R.Length
Main():void=
    C:=cell{{}}
    R:=Run(C,{value})
    Print("result {{R}} state {{C.N}}")''')
    lines = ['arg 1'] + [f'value {i}' for i in range(n, -1, -1)] + [f'result {n+1} state 1']
elif mode == 4:
    bind = 'F:=Bind(D.V,D.Other)\n        ' if control else ''
    f = 'F' if control else 'Same'
    print(f'''Same(X:t where t:subtype(comparable))<computes>:t=X
Bind(X:a,Y:b where a:subtype(comparable),b:subtype(comparable))<computes>:type{{_(:a,:b)<computes>:tuple(a,b)}}=Same
Twice(F:type{{_(:a,:b)<computes>:tuple(a,b)}},X:a,Y:b where a:subtype(comparable),b:subtype(comparable))<computes>:tuple(a,b)=F(X,Y)|F(X,Y)
root(t:type):=class{{V:t;N:int}}
extra(a:subtype(comparable),b:subtype(comparable)):=class(root(a)){{Other:b}}
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        {bind}R:=for(V:=Twice({f},D.V,D.Other)):
            if(V(0)=D.V,V(1)=D.Other)then 1 else 0
        Print("opened {{D.N}} {{R.Length}}")
    else:
        Print("base {{P.N}}")
Main():void=
    Use(extra({ty},int){{V:={value},Other:=3,N:={n}}})
    Use(root(int){{V:=7,N:={n+1}}})''')
    lines = [f'opened {n} 2', f'base {n+1}']
else:
    print('''UseGlobal():int=block{F:type{_(:int)<computes>:int}=Id;F(1)}
Show(X:int)<computes>:string="show {X}"
Duplicate(F:type{_(:int)<computes>:t},X:int where t:type)<computes>:t=F(X)|F(X)
Shadow(Id:type{_(:int)<computes>:string}):[]string=for{Duplicate(Id,3)}
reader:=class:
    (reader:)Id:type{_(:int)<computes>:string}=Show
    Read():[]string=for{Duplicate((reader:)Id,6)}
Main():void=
    A:=Shadow(Show)
    B:=reader{}.Read()
    for(S:A):Print(S)
    for(S:B):Print(S)''')
    lines = ['show 3', 'show 3', 'show 6', 'show 6']

Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
