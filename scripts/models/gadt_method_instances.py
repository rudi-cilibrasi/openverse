#!/usr/bin/env python3
"""Bound generic method instances behave as ordinary receiver calls.

The oracle models receiver state, call order, rollback and async cleanup.
--control emits direct calls for the compiler before generic method values.
"""
import random
import sys
from pathlib import Path

rng = random.Random(int(sys.argv[1]))
control = '--control' in sys.argv[3:]
mode = rng.randrange(5)
ty, v, w = rng.choice([('int', str(rng.randrange(1, 8)), str(rng.randrange(10, 18))),
                       ('string', '"old"', '"new"')])
other, x = rng.choice([('int', str(rng.randrange(20, 30))), ('string', '"input"')])
shown = lambda s: s.strip('"')
n = rng.randrange(2, 8)
lines = []
print('cell:=class{var N:int=0}')

if mode == 0:
    bind = 'Receiver:=Touch(B)' if control else '''F:type{_(:b):tuple(u,b)}=Touch(B).Pair
    G:type{_(:[]b):[]b}=B.Copy'''
    pair = 'Receiver.Pair(X)' if control else 'F(X)'
    copy = 'Receiver.Copy(array{R(1)})' if control else 'G(array{R(1)})'
    print(f'''box(t:type):=class:
    var V:t
    C:cell
    Pair(X:u where u:type):tuple(t,u)=
        set C.N+=1
        Print("pair {{C.N}}")
        (V,X)
    Copy(X:[]u where u:type):[]u=
        set C.N+=1
        Print("copy {{C.N}}")
        X
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {{B.C.N}}")
    B
Run(B:box(u),X:b,Next:u where u:type,b:type):tuple(u,b,int)=
    {bind}
    set B.V=Next
    R:={pair}
    E:={copy}
    (R(0),R(1),E.Length)
Main():void=
    R:=Run(box({ty}){{V:={v},C:=cell{{}}}},{x},{w})
    Print("result {{R(0)}} {{R(1)}} {{R(2)}}")''')
    lines = ['receiver 1', 'pair 2', 'copy 3', f'result {shown(w)} {shown(x)} 1']
elif mode == 1:
    bind = '' if control else 'F:type{_(:u,:u)<transacts><decides>:u}=B.Match\n    '
    call = lambda val: f'B.Match[{val},X]' if control else f'F[{val},X]'
    print(f'''box(t:type):=class:
    V:t
    C:cell
    Match(X:v,Y:v where v:subtype(comparable))<transacts><decides>:v=
        set C.N+=1
        Print("try {{C.N}}")
        X=Y
        X
Run(B:box(t),X:u,Y:u where t:type,u:subtype(comparable))<transacts>:void=
    {bind}if({call('Y')})then Print("wrong")else Print("miss {{B.C.N}}")
    if({call('X')},Print("suffix"),false?)then Print("wrong")else Print("reject {{B.C.N}}")
    if({call('X')})then Print("hit {{B.C.N}}")else Print("wrong")
Main():void=Run(box(string){{V:="tag",C:=cell{{}}}},{v},{w})''')
    lines = ['miss 0', 'reject 0', 'try 1', 'hit 1']
elif mode == 2:
    bind = '' if control else '''F:type{_(:b):tuple(u,b)}=P.Pair
    G:type{_(:int):[]b}=P.Empty
    '''
    pair = 'P.Pair(X)' if control else 'F(X)'
    empty = 'P.Empty(0)' if control else 'G(0)'
    print(f'''source(t:type):=interface:
    Get():t
    Pair(X:u where u:type):tuple(t,u)=(Get(),X)
    Empty(N:int where u:type):[]u=array{{}}
mixed(a:type,b:type):=class(source([]b)):
    Extra:a
    V:b
    Get<override>():[]b=array{{V}}
Run(P:source(u),X:b where u:type,b:type):tuple(u,b,int)=
    {bind}R:={pair}
    E:[]b={empty}
    (R(0),R(1),E.Length)
Main():void=
    R:=Run(mixed(int,{ty}){{Extra:={n},V:={v}}},{x})
    Print("result {{R(0).Length}} {{R(1)}} {{R(2)}}")''')
    lines = [f'result 1 {shown(x)} 0']
elif mode == 3:
    bind = 'Receiver:=Touch(B)' if control else 'F:type{_(:[]u)<suspends>:[]u}=Touch(B).Later'
    call = 'Receiver.Later(array{X,X})' if control else 'F(array{X,X})'
    print(f'''box(t:type):=class:
    V:t
    C:cell
    Later(X:[]u where u:type)<suspends>:[]u=
        set C.N+=1
        Print("begin {{C.N}}")
        defer: Print("cleanup {{C.N}}")
        Sleep(1.0)
        Print("end {{C.N}}")
        X
Touch(B:box(t) where t:type):box(t)=
    set B.C.N+=1
    Print("receiver {{B.C.N}}")
    B
Run(B:box(t),X:u where t:type,u:type)<suspends>:void=
    {bind}
    T:=spawn{{{call}}}
    E:=T.Await()
    Print("done {{E.Length}}")
    race:
        {call}
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished")
Main()<suspends>:void=Run(box({ty}){{V:={v},C:=cell{{}}}},{x})''')
    lines = ['receiver 1', 'begin 2', 'end 2', 'cleanup 2', 'done 2', 'begin 3', 'cancel', 'cleanup 3', 'finished']
else:
    factory = '' if control else 'Bind(X:u where u:type):type{_(:u):u}=Echo\n'
    bind = '' if control else 'F:=B.Bind(X)\n    '
    call = 'B.Echo(X)' if control else 'F(X)'
    print(f'''box(t:type):=class:
    V:t
    C:cell
    Echo(X:u where u:type):u=
        set C.N+=1
        Print("echo {{C.N}}")
        X
    {factory}
Run(B:box(u),X:b where u:type,b:type):b=
    {bind}set B.C.N+={n}
    A:={call}
    set B.C.N+={n}
    {call}
Main():void=Print("result {{Run(box({ty}){{V:={v},C:=cell{{}}}},{x})}}")''')
    lines = [f'echo {n+1}', f'echo {2*n+2}', f'result {shown(x)}']

Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
