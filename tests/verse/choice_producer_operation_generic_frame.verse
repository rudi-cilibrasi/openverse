# Preserve producer/consumer order, cleanup and storage across shared operations (#335).
a:=class:
    N:int=1
    M():int=
        Print("a start")
        defer{Print("a cleanup")}
        (block{Print("a first");N})|(block{Print("a second");N+10})
b:=class:
    N:int=2
    M():int=
        Print("b start")
        defer{Print("b cleanup")}
        (block{Print("b first");N})|(block{Print("b second");N+10})
Dup(X:t where t:type)<computes>:t=X|X
Use(V:t where t:type)<suspends>:t=
    var State:t=V
    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()):
        Sleep(0.001)
        set State=V
        X+Y
    Print("generic {Rows.Length}")
    State
Main()<suspends>:void=
    Print("int {Use(7)}")
    Print("string {Use("ok")}")
