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
Main()<suspends>:void=
    race:
        block:
            Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()):
                defer{Print("body cleanup")}
                Print("body {X} {Y}")
                Sleep(0.1)
                X+Y
            Print("rows {Rows.Length}")
        block:
            Sleep(0.25)
            Print("timeout")
    Print("done")
