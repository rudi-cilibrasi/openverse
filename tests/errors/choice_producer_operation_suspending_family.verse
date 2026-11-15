# expect: has several values, but it is <suspends>: such methods are not supported yet (#283)
a:=class<computes>:
    N:int=1
    M()<suspends>:int=
        Sleep(0.001)
        N|(N+10)
b:=class<computes>:
    N:int=2
    M()<suspends>:int=
        Sleep(0.001)
        N|(N+10)
Dup(V:t where t:type)<computes>:t=V|V
Main()<suspends>:void=
    Rows:=for(A0:=Dup(a{})|Dup(b{}),X0:=A0.M()):X0+A0.N
    var Sum:int=0
    for(R:Rows):set Sum+=R
    Print("{Rows.Length} {Sum}")
