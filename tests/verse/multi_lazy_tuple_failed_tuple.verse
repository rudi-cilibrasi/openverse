counter := class { var N:int=0 }
Next(N:int,C:counter)<transacts><decides>:int =
    set C.N+=1
    Print("edge {N}")
    N>1
    N-1
Walk(N:int,C:counter)<transacts><decides>:int =
    N>=0
    Print("visit {N}")
    if(N>0)then(N | Walk[(Next[N,C],C)] | N+10)else 0
Main()<transacts>:void =
    C:=counter{}
    for(V:=Walk[2,C]){Print("all {V} {C.N}")}
    Print("after {C.N}")
    if(V:=Walk[2,C],V>10)then Print("first {V} {C.N}")
    if(V:=Walk[2,C],V<0)then Print("bad")else Print("none {C.N}")
