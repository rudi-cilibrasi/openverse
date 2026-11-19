# Preserve uncaught failure and the real outer rollback boundary (#335).
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
cell:=class{var N:int=10}
Use(C:cell)<transacts><decides>:void=
    Rows:=for(A:=Dup(a{})|Dup(b{}),X:=A.M(),B:=Dup(a{})|Dup(b{}),Y:=B.M()):
        defer{Print("cleanup {C.N}")}
        set C.N+=1
        Print("body {C.N}")
        C.N<12
        X+Y
    Print("bad {Rows.Length}")
Main():void=
    C:=cell{}
    if(Use[C])then Print("bad success")else Print("rolled back {C.N}")
