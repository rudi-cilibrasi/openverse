counter := class { var N:int=0 }
box(t:type) := class:
    C:counter
    Next()<transacts>:box(t) =
        set C.N+=1
        Print("receiver {C.N}")
        Self
    Arg(N:int)<transacts>:int =
        set C.N+=1
        Print("tuple {C.N}")
        N-1
    Walk(X:t,N:int)<transacts>:t =
        Print("visit {N}")
        if(N<=0):
            Print("base")
            Result:=X
            return Result
        Print("descend")
        return X | Next().Walk((X,Arg(N)))
Main()<transacts>:void =
    C:=counter{}
    B:=box(int){C:=C}
    for(V:=B.Walk(7,2)){Print("all {V} {C.N}")}
    if(V:=B.Walk(7,2))then Print("first {V} {C.N}")
    if(V:=B.Walk(7,2),V>8)then Print("bad")else Print("none {C.N}")
