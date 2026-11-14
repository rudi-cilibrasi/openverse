#!/usr/bin/env python3
"""Generic function instances retain values, bounds and call effects.

The oracle models ordinary functions and transactional/scheduler output.
--control emits direct generic calls for the compiler before open values.
"""
import random
import sys
from pathlib import Path

rng = random.Random(int(sys.argv[1]))
control = '--control' in sys.argv[3:]
mode = rng.randrange(5)
ty, x, y = rng.choice([
    ('int', str(rng.randrange(1, 10)), str(rng.randrange(11, 20))),
    ('string', '"old"', '"new"'),
])
shown = lambda s: s.strip('"')
n = rng.randrange(2, 8)
lines = []

if mode == 0:
    binds = '' if control else '''F:type{_(:t)<computes>:t}=Id
    G:type{_(:t,:u)<computes>:tuple(u,t)}=Swap
    H:type{_(:t)<computes>:[]t}=Empty
    '''
    a = 'Id(X)' if control else 'F(X)'
    pair = f'Swap({a},Y)' if control else f'G({a},Y)'
    # (a parameter gives Empty's type parameter: the Book's rule, error
    # 3503, no longer the expected result)
    empty = 'Empty(X)' if control else 'H(X)'
    print(f'''Id(X:a where a:type)<computes>:a=X
Swap(X:a,Y:b where a:type,b:type)<computes>:tuple(b,a)=(Y,X)
Empty(N:a where a:type)<computes>:[]a=array{{}}
Run(X:t,Y:u where t:type,u:type)<computes>:tuple(u,t,int)=
    {binds}P:={pair}
    E:[]t={empty}
    (P(0),P(1),E.Length)
Main():void=
    R:=Run({x},{n})
    S:=Run({y},"tag")
    Print("{{R(0)}} {{R(1)}} {{R(2)}}")
    Print("{{S(0)}} {{S(1)}} {{S(2)}}")''')
    lines = [f'{n} {shown(x)} 0', f'tag {shown(y)} 0']
elif mode == 1:
    bind = '' if control else 'F:type{_(:cell,:t,:t)<transacts><decides>:t}=Match\n    '
    call = lambda a: f'Match[C,{a},X]' if control else f'F[C,{a},X]'
    print(f'''cell:=class{{var N:int=0}}
Match(C:cell,X:a,Y:a where a:subtype(comparable))<transacts><decides>:a=
    set C.N+=1
    Print("try {{C.N}}")
    X=Y
    X
Run(X:t,Y:t where t:subtype(comparable))<transacts>:void=
    C:=cell{{}}
    {bind}if(V:={call('Y')})then Print("bad")else Print("miss {{C.N}}")
    if(V:={call('X')},Print("suffix"),false?)then Print("bad")else Print("reject {{C.N}}")
    if(V:={call('X')})then Print("hit {{C.N}}")else Print("bad")
Main():void=Run({x},{y})''')
    lines = ['miss 0', 'reject 0', 'try 1', 'hit 1']
elif mode == 2:
    bind = '' if control else 'F:=Bind(D.B)\n        '
    call = 'Id(D.B)' if control else 'F(D.B)'
    maker = '' if control else 'Bind(X:t where t:type):type{_(:t):t}=Id\n'
    print(f'''Id(X:t where t:type):t=X
{maker}root:=class{{N:int}}
extra(a:subtype(comparable),b:type):=class(root):
    A:a
    B:b
Run(P:root):void=
    if(D:=extra[P]):
        {bind}V:={call}
        E:=array{{V,D.B}}
        Print("opened {{D.N}} {{E.Length}}")
    else:
        Print("base {{P.N}}")
Main():void=
    Run(extra(int,{ty}){{N:={n},A:=1,B:={x}}})
    Run(extra(string,{ty}){{N:={n+1},A:="a",B:={y}}})
    Run(root{{N:={n+2}}})''')
    lines = [f'opened {n} 2', f'opened {n+1} 2', f'base {n+2}']
elif mode == 3:
    maker = '' if control else 'Bind(X:t where t:type):type{_(:cell,:t)<suspends>:t}=Later\n'
    bind = '' if control else 'F:=Bind(X)\n    '
    call = 'Later(C,X)' if control else 'F(C,X)'
    print(f'''cell:=class{{var N:int=0}}
Later(C:cell,X:t where t:type)<suspends>:t=
    set C.N+=1
    Print("begin {{C.N}}")
    defer: Print("cleanup {{C.N}}")
    Sleep(1.0)
    Print("end {{C.N}}")
    X
{maker}Run(X:t where t:type)<suspends>:void=
    C:=cell{{}}
    {bind}T:=spawn{{{call}}}
    V:=T.Await()
    Print("done {{C.N}}")
    race:
        {call}
        block:
            Sleep(0.5)
            Print("cancel")
    Print("finished {{C.N}}")
Main()<suspends>:void=Run({x})''')
    lines = ['begin 1', 'end 1', 'cleanup 1', 'done 1', 'begin 2', 'cancel', 'cleanup 2', 'finished 2']
else:
    field = '' if control else 'F:type{_(:t):t}=Id\n    '
    call = 'Id(V)' if control else 'F(V)'
    print(f'''Id(X:t where t:type):t=X
holder(t:type):=class:
    var V:t
    {field}Go():t={call}
Make(X:t where t:type):holder(t)=holder(t){{V:=X}}
Main():void=
    B:=Make({x})
    Print("before {{B.Go()}}")
    set B.V={y}
    Print("after {{B.Go()}}")
    S:=Make(array{{{x},{y}}})
    Print("nested {{S.Go().Length}}")''')
    lines = [f'before {shown(x)}', f'after {shown(y)}', 'nested 2']

Path(sys.argv[2]).write_text('exit=0\n' + '\n'.join(lines) + '\n')
