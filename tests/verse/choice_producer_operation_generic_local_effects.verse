# Preserve typed later-local arguments, default effects and waiting order (#335).
cell:=class{var Count:int=0}
Arg(C:cell,N:int)<transacts>:int=
    set C.Count+=1
    Print("arg {N} step {C.Count}")
    N+1
Default(N:int)<transacts>:int=
    Print("default {N}")
    N+3
a:=class:
    N:int=1
    M(V:t,?D:int=Default(N) where t:type)<transacts>:t=
        Print("a start {D}")
        defer{Print("a cleanup {D}")}
        V|V
b:=class:
    N:int=2
    M(V:t,?D:int=Default(N) where t:type)<transacts>:t=
        Print("b start {D}")
        defer{Print("b cleanup {D}")}
        V|V
Dup(V:t where t:type)<computes>:t=V|V
Main()<suspends>:void=
    C:=cell{}
    Rows:=for(A:=Dup(a{})|Dup(b{}),Z:=Arg(C,A.N),X:=A.M(Z),B:=Dup(a{})|Dup(b{}),W:=Arg(C,B.N),Y:=B.M(W)):
        Sleep(0.001)
        Print("body {X} {A.N} {Y} {B.N}")
        X+A.N+Y+B.N
    var Sum:int=0
    for(R:Rows):set Sum+=R
    Print("{Rows.Length} {Sum} {C.Count}")
