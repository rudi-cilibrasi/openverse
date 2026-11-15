# Preserve producer/consumer order, cleanup and storage across shared operations (#335).
Default(N:int):int=
    Print("default {N}")
    N+3
Arg(N:int):int=
    Print("arg {N}")
    N
Many(N:int):int=
    Print("many {N}")
    N|(N+100)
Early(N:int):int=
    Print("early {N}")
    if(N<0):return N
    N|(N+100)
Gate(N:int)<decides>:int=
    Print("gate {N}")
    N>0
    N
a:=class:
    N:int=1
    M(V:int,?D:int=Default(N)):int=
        Print("a start {V} {D}")
        defer{Print("a cleanup")}
        (V+N+D)|(V+N+D+10)
b:=class:
    N:int=2
    M(V:int,?D:int=Default(N)):int=
        Print("b start {V} {D}")
        defer{Print("b cleanup")}
        (V+N+D)|(V+N+D+10)
Dup(X:t where t:type)<computes>:t=X|X
Main()<suspends>:void=
    var State:int=10
    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(block{set State+=1;Print("state {State}");State}),B:=Dup(a{})|Dup(b{}),Y:=B.M(X)):
        Sleep(0.001)
        Print("body state {State}")
        set State+=X+Y
        State
    Print("rows {Rows.Length} state {State}")
