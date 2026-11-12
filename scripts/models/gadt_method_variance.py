#!/usr/bin/env python3
"""Generic-receiver variance agrees with explicit source-level adapters.

Independent state/order/rollback/cleanup oracles; --control uses an adapter
whose declared signature is already the target type, for pre-change compilers.
"""
import random
import sys
from pathlib import Path

rng = random.Random(int(sys.argv[1]))
control = '--control' in sys.argv[3:]
mode = rng.randrange(6)
ty, old, new = rng.choice([('int', str(rng.randrange(1, 9)), str(rng.randrange(12, 20))),
                           ('string', '"old"', '"new"')])
n, x = rng.randrange(2, 8), rng.randrange(10, 20)
shown = lambda s: s.strip('"')
print('cell:=class{var N:int=0}')

if mode == 0:
    value = 'adapter(t){B:=Touch(B)}.Call' if control else 'Touch(B).Pair'
    print(f'''box(t:type):=class:
    var V:t
    C:cell
    Pair(X:rational):tuple(t,int)=
        set C.N+=1
        Print("pair {{C.N}} {{Floor(X)}}")
        (V,C.N)
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {{B.C.N}}")
    B
adapter(t:type):=class<computes>:
    B:box(t)
    Call(X:int):tuple(t,rational)=
        R:tuple(t,int)=B.Pair(X)
        R
Bind(B:box(t) where t:type):type{{_(:int):tuple(t,rational)}}={value}
Arg(C:cell,X:int):int=
    set C.N+=1
    Print("arg {{C.N}}")
    X
Run(B:box(t),Next:t where t:type):tuple(t,rational)=
    F:=Bind(B)
    set B.V=Next
    set B.C.N+={n}
    F(Arg(B.C,{x}))
Main():void=
    R:=Run(box({ty}){{V:={old},C:=cell{{}}}},{new})
    Print("result {{R(0)}} {{Floor(R(1))}}")''')
    lines = ['receiver 1', f'arg {n+2}', f'pair {n+3} {x}', f'result {shown(new)} {n+3}']
elif mode == 1:
    value = 'adapter(t){B:=B}.Call' if control else 'B.Match'
    print(f'''box(t:subtype(comparable)):=class:
    V:t
    C:cell
    Match(X:t)<transacts><decides>:tuple(t,int)=
        set C.N+=1
        Print("try {{C.N}}")
        X=V
        (X,C.N)
adapter(t:subtype(comparable)):=class<computes>:
    B:box(t)
    Call(X:t)<transacts><decides>:tuple(t,rational)=
        R:tuple(t,int)=B.Match[X]
        R
Bind(B:box(t) where t:subtype(comparable))<computes>:type{{_(:t)<transacts><decides>:tuple(t,rational)}}={value}
Run(B:box(t),Other:t where t:subtype(comparable))<transacts>:void=
    F:=Bind(B)
    if(F[Other])then Print("wrong")else Print("miss {{B.C.N}}")
    if(F[B.V],Print("suffix"),false?)then Print("wrong")else Print("reject {{B.C.N}}")
    if(R:=F[B.V],R(0)=B.V)then Print("hit {{Floor(R(1))}} {{B.C.N}}")else Print("wrong")
Main():void=Run(box({ty}){{V:={old},C:=cell{{}}}},{new})''')
    lines = ['miss 0', 'reject 0', 'try 1', 'hit 1 1']
elif mode == 2:
    value = 'adapter(t){B:=B}.Call' if control else 'B.Make'
    print(f'''animal(t:type):=class<computes>{{V:t}}
dog(t:type):=class<computes>(animal(t)){{N:int={n}}}
source(t:type):=interface:
    Get():t
    Make(X:animal(t))<computes>:dog(t)=dog(t){{V:=X.V}}
box(t:type,h:type):=class(source(t)):
    V:t
    Hidden:h
    Get<override>():t=V
adapter(t:type):=class<computes>:
    B:source(t)
    Call(X:dog(t))<computes>:animal(t)=
        R:dog(t)=B.Make(X)
        R
Bind(B:source(t) where t:type)<computes>:type{{_(:dog(t))<computes>:animal(t)}}={value}
Main():void=
    B:=box({ty},string){{V:={old},Hidden:="hidden"}}
    F:=Bind(B)
    R:=F(dog({ty}){{V:={new}}})
    Print("result {{R.V}}")''')
    lines = [f'result {shown(new)}']
elif mode == 3:
    value = 'adapter(t,u){B:=B}.Call' if control else 'B.Pair'
    print(f'''root(t:type):=class{{V:t}}
extra(a:subtype(comparable),b:subtype(comparable)):=class(root(a)):
    Hidden:b
    Pair(P:tuple(a,rational))<computes>:tuple(b,int)=(Hidden,Floor(P(1)))
adapter(a:subtype(comparable),b:subtype(comparable)):=class<computes>:
    B:extra(a,b)
    Call(X:a,Y:int)<computes>:tuple(b,rational)=
        R:tuple(b,int)=B.Pair((X,Y))
        R
Bind(B:extra(t,u) where t:subtype(comparable),u:subtype(comparable))<computes>:type{{_(:t,:int)<computes>:tuple(u,rational)}}={value}
Use(P:root(t) where t:type):void=
    if(D:=extra[P]):
        F:=Bind(D)
        R:=F(D.V,{x})
        if(R(0)=D.Hidden)then Print("opened {{Floor(R(1))}}")else Print("wrong")
    else:
        Print("base")
Main():void=
    Use(extra({ty},int){{V:={old},Hidden:={n}}})
    Use(extra(int,{ty}){{V:={x},Hidden:={new}}})
    Use(root(int){{V:=0}})''')
    lines = [f'opened {x}', f'opened {x}', 'base']
elif mode == 4:
    value = 'adapter(t){B:=Touch(B)}.Call' if control else 'Touch(B).Later'
    print(f'''box(t:type):=class:
    V:t
    C:cell
    Later(X:rational)<suspends>:tuple(t,int)=
        set C.N+=1
        Print("begin {{C.N}} {{Floor(X)}}")
        defer: Print("cleanup {{C.N}}")
        Sleep(1.0)
        Print("end {{C.N}}")
        (V,C.N)
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {{B.C.N}}")
    B
adapter(t:type):=class<computes>:
    B:box(t)
    Call(X:int)<suspends>:tuple(t,rational)=
        R:tuple(t,int)=B.Later(X)
        R
Bind(B:box(t) where t:type):type{{_(:int)<suspends>:tuple(t,rational)}}={value}
Run(B:box(t) where t:type)<suspends>:void=
    F:=Bind(B)
    T:=spawn{{F({x})}}
    R:=T.Await()
    Print("done {{Floor(R(1))}}")
    race:
        F({x+1})
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished {{B.C.N}}")
Main()<suspends>:void=Run(box({ty}){{V:={old},C:=cell{{}}}})''')
    lines = ['receiver 1', f'begin 2 {x}', 'end 2', 'cleanup 2', 'done 2', f'begin 3 {x+1}', 'cancel', 'cleanup 3', 'finished 3']
else:
    value = 'adapter(t){B:=B}.Call' if control else 'B.Pair'
    print(f'''box(t:type):=class:
    V:t
    Pair(X:rational)<computes>:tuple(t,int)=(V,Floor(X))
adapter(t:type):=class<computes>:
    B:box(t)
    Call(X:int)<computes>:tuple(t,rational)=
        R:tuple(t,int)=B.Pair(X)
        R
Bind(B:box(t) where t:type)<computes>:type{{_(:int)<computes>:tuple(t,rational)}}={value}
holder(t:type):=class<computes>:
    B:box(t)
    F:type{{_(:int)<computes>:tuple(t,rational)}}
Call(B:box(t),?F:type{{_(:int)<computes>:tuple(t,rational)}}=Bind(B) where t:type)<computes>:tuple(t,rational)=F({x})
Twice(F:type{{_(:int)<computes>:tuple(t,rational)}},X:int where t:type)<computes>:tuple(t,rational)=F(X)|F(X+1)
Run(B:box(t) where t:type):void=
    H:=holder(t){{B:=B,F:=Bind(B)}}
    R:=Call(B)
    Print("default {{Floor(R(1))}}")
    Values:=for(V:=Twice(H.F,{x})):Floor(V(1))
    for(N:Values):Print("value {{N}}")
Main():void=Run(box({ty}){{V:={old}}})''')
    lines = [f'default {x}', f'value {x}', f'value {x+1}']

Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
