# Preserve producer/consumer order, cleanup and storage across shared operations (#335).
Default(N:int)<transacts>:int=
    Print("default {N}")
    N+3
Arg(N:int)<transacts>:int=
    Print("arg {N}")
    N
Many(N:int):int=
    Print("many {N}")
    N|(N+100)
Early(N:int):int=
    Print("early {N}")
    if(N<0):return N
    N|(N+100)
Gate(N:int)<transacts><decides>:int=
    Print("gate {N}")
    N>0
    N
a:=class:
    N:int=1
    M(V:int,?D:int=Default(N))<transacts>:int=
        Print("a start {V} {D}")
        defer{Print("a cleanup")}
        (V+N+D)|(V+N+D+10)
b:=class:
    N:int=2
    M(V:int,?D:int=Default(N))<transacts>:int=
        Print("b start {V} {D}")
        defer{Print("b cleanup")}
        (V+N+D)|(V+N+D+10)
Dup(X:t where t:type)<computes>:t=X|X
Main()<suspends>:void=
    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(Gate[A.N-1]),B:=Dup(a{})|Dup(b{}),Y:=B.M(Arg(X))):
        Sleep(0.001)
        Print("body {X} {Y}")
        X+Y
    Print("rows {Rows.Length}")
