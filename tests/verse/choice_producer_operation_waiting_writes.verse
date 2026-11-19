# Preserve producer/consumer order, cleanup and storage across shared operations (#335).
a:=class:
    N:int=1
    M()<transacts>:int=
        Print("a start")
        defer{Print("a cleanup")}
        (block{Print("a first");N})|(block{Print("a second");N+10})
b:=class:
    N:int=2
    M()<transacts>:int=
        Print("b start")
        defer{Print("b cleanup")}
        (block{Print("b first");N})|(block{Print("b second");N+10})
Dup(X:t where t:type)<computes>:t=X|X
Main()<suspends>:void=
    var State:int=10
    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()):
        Sleep(0.001)
        set State+=X+Y
        Print("body {State}")
        State
    Print("rows {Rows.Length} state {State}")
