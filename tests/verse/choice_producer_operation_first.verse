# A heterogeneous producer must run its consumer before advancing.
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
Main():void=
    if(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M(),X+Y>20,Z:=X+A.N+Y+B.N):Print("found {Z}")
