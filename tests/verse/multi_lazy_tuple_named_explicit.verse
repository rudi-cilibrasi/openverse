counter := class { var N:int=0 }
Note(N:int,C:counter)<transacts>:int =
    set C.N+=1
    Print("note {N}")
    N
Walk(N:int,C:counter,?D:int=0)<transacts>:int =
    Print("visit {N} {D}")
    if(N>0)then(D | Walk((Note(N-1,C),C),?D:=Note(N+10,C)))else D
Main()<transacts>:void =
    C:=counter{}
    for(V:=Walk(2,C)){Print("all {V} {C.N}")}
    if(V:=Walk(2,C),V>10)then Print("first {V} {C.N}")
