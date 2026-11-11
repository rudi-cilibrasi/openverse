Note(N:int,C:counter)<transacts>:int =
    set C.N+=1
    Print("note {N}")
    N
counter := class { var N:int=0 }
Walk(N:int,A:int,C:counter,?D:int=Note(A,C))<transacts>:int =
    Print("visit {N} {D}")
    if(N>0)then(D | Walk((Note(N-1,C),A+1,C)))else D
Main()<transacts>:void =
    C:=counter{}
    for(V:=Walk(2,5,C,?D:=0)){Print("all {V} {C.N}")}
    if(V:=Walk(2,5,C),V=7)then Print("first {V} {C.N}")
