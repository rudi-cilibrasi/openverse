#!/usr/bin/env python3
"""Bound methods retain their receiver and ordinary call/rollback behavior.

The oracle models calls, counters and scheduler order, independently of type
representation or dispatch lowering. --control emits direct calls on a captured
receiver for comparison with a compiler predating generic method-value shapes.
"""
import random
import sys
from pathlib import Path

rng = random.Random(int(sys.argv[1]))
control = '--control' in sys.argv[3:]
mode = rng.randrange(5)
ty, v, x = rng.choice([('int', str(rng.randrange(1, 8)), str(rng.randrange(10, 18))),
                       ('string', '"old"', '"new"')])
extra_ty, extra = rng.choice([('int', '4'), ('string', '"extra"'), ('tuple(int,string)', '(4,"extra")')])
show = lambda value: value.strip('"')
code = rng.randrange(20, 40)
bound = rng.choice(['type', 'subtype(comparable)'])
check = 'if(V=V)then V else V' if bound != 'type' else 'V'
lines = []
print('cell:=class{var N:int=0}')

if mode == 0:
    capture = 'Receiver:=Touch(B)' if control else 'F:=Touch(B).Same\n    G:=B.Nested\n    H:=B.Pair\n    K:=B.Size'
    call = lambda method, alias, arg='': f'Receiver.{method}({arg})' if control else f'{alias}({arg})'
    print(f'''box(t:{bound},u:type):=class:
    var V:t
    Extra:u
    C:cell
    Same(X:t)<transacts>:t=
        set C.N+=1
        Print("same {{C.N}}")
        {check}
    Nested(X:[]t)<transacts>:[]t=
        set C.N+=1
        Print("nested {{C.N}}")
        X
    Pair(X:t)<transacts>:tuple(t,t)=
        set C.N+=1
        Print("pair {{C.N}}")
        (V,X)
    Size()<transacts>:int=
        set C.N+=1
        Print("size {{C.N}}")
        {code}+C.N
Touch(B:box(a,b) where a:{bound},b:type)<transacts>:box(a,b)=
    set B.C.N+=1
    Print("receiver {{B.C.N}}")
    B
Run(B:box(a,b),X:a where a:{bound},b:type)<transacts>:tuple(a,a,a,a,int,int)=
    {capture}
    Before:=B.V
    set B.V=X
    Y:={call('Same','F','Before')}
    E:={call('Nested','G','array{Y}')}
    P:={call('Pair','H','Before')}
    S:={call('Size','K')}
    (Y,P(0),P(1),E[0] or Y,S,B.C.N)
Main():void=
    R:=Run(box({ty},{extra_ty}){{V:={v},Extra:={extra},C:=cell{{}}}},{x})
    Print("result {{R(0)}} {{R(1)}} {{R(2)}} {{R(3)}} {{R(4)}} {{R(5)}}")''')
    lines = ['receiver 1', 'same 2', 'nested 3', 'pair 4', 'size 5',
             f'result {show(x)} {show(x)} {show(v)} {show(x)} {code+5} 5']
elif mode == 1:
    capture = 'Receiver:=Touch(B)' if control else 'F:=Touch(B).Keep'
    call = lambda value: f'Receiver.Keep[{value}]' if control else f'Apply[F,{value}]'
    print(f'''box(t:subtype(comparable),u:type):=class:
    V:t
    Extra:u
    C:cell
    Keep(X:t)<transacts><decides>:t=
        set C.N+=1
        Print("try {{C.N}}")
        X=V
        X
Touch(B:box(a,b) where a:subtype(comparable),b:type)<transacts>:box(a,b)=
    set B.C.N+=1
    Print("receiver {{B.C.N}}")
    B
Apply(F:type{{_(:a)<transacts><decides>:b}},X:a where a:type,b:type)<transacts><decides>:b=F[X]
Run(B:box(a,b),Wrong:a where a:subtype(comparable),b:type)<transacts>:void=
    {capture}
    if(Y:={call('Wrong')})then Print("bad")else Print("miss {{B.C.N}}")
    if(Y:={call('B.V')},Print("suffix"),false?)then Print("bad")else Print("reject {{B.C.N}}")
    if(Y:={call('B.V')})then Print("hit {{B.C.N}}")else Print("bad")
Main():void=Run(box({ty},{extra_ty}){{V:={v},Extra:={extra},C:=cell{{}}}},{x})''')
    lines = ['receiver 1', 'miss 1', 'reject 1', 'try 2', 'hit 2']
elif mode == 2:
    fixed = rng.choice([True, False])
    receiver = f'child({ty}){{Marker:=4,V:={v}}}' if fixed else f'mixed(int,{ty}){{Marker:=4,V:={v}}}'
    capture = '' if control else 'F:=P.Same\n    '
    call = 'P.Same(X)' if control else 'Apply(F,X)'
    print(f'''head(a:type):=interface{{Head():a}}
sink(b:type):=interface{{Same(X:b)<transacts>:b}}
mixed(k:type,t:subtype(comparable)):=class(head(k),sink([]t)):
    Marker:k
    V:t
    Head<override>():k=Marker
    Same<override>(X:[]t)<transacts>:[]t=
        Print("view")
        if(V=V)then X+array{{V}} else X
child(z:subtype(comparable)):=class(mixed(int,z)){{}}
Apply(F:type{{_(:a)<transacts>:b}},X:a where a:type,b:type)<transacts>:b=F(X)
Run(P:sink(a),X:a where a:type)<transacts>:a=
    {capture}{call}
Main():void=
    R:=Run({receiver},array{{{x}}})
    Print("result {{R.Length}} {{R[0] or {x}}} {{R[1] or {v}}}")''')
    lines = ['view', f'result 2 {show(x)} {show(v)}']
elif mode == 3:
    capture = 'Receiver:=B' if control else 'F:=B.Wait'
    call = 'Receiver.Wait(X)' if control else 'F(X)'
    print(f'''box(t:type,u:type):=class:
    V:t
    Extra:u
    C:cell
    Wait(X:[]t)<suspends><transacts>:[]t=
        defer:Print("cleanup {{C.N}}")
        set C.N+=1
        Print("begin {{C.N}}")
        Sleep(0.001)
        Print("end {{C.N}}")
        X+array{{V}}
Run(B:box(a,b),X:[]a where a:type,b:type)<suspends><transacts>:[]a=
    {capture}
    {call}
Main()<suspends>:void=
    C:=cell{{}}
    B:=box({ty},{extra_ty}){{V:={v},Extra:={extra},C:=C}}
    T:=spawn{{Run(B,array{{{x}}})}}
    Print("created {{C.N}}")
    R:=T.Await()
    Print("result {{R.Length}} {{R[0] or {x}}} {{R[1] or {v}}} {{C.N}}")''')
    lines = ['begin 1', 'created 1', 'end 1', 'cleanup 1', f'result 2 {show(x)} {show(v)} 1']
else:
    capture = 'Receiver:=Touch(B)' if control else 'F:=Touch(B).Size'
    call = 'Receiver.Size()' if control else 'F()'
    print(f'''marker(t:type,u:type):=class:
    C:cell
    Size()<transacts>:int=
        set C.N+=1
        Print("size {{C.N}}")
        {code}+C.N
Touch(B:marker(a,b) where a:type,b:type)<transacts>:marker(a,b)=
    set B.C.N+=1
    Print("receiver {{B.C.N}}")
    B
Run(B:marker(a,b) where a:type,b:type)<transacts>:int=
    {capture}
    A:={call}
    D:={call}
    A+D
Main():void=Print("result {{Run(marker({ty},{extra_ty}){{C:=cell{{}}}})}}")''')
    lines = ['receiver 1', 'size 2', 'size 3', f'result {2*code+5}']

Path(sys.argv[2]).write_text('exit=0\n'+'\n'.join(lines)+'\n')
