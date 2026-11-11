counter := class { var N:int=0 }
Note(N:int,C:counter)<transacts>:int =
    set C.N+=1
    Print("note {N}")
    N
Walk(N:int,C:counter,?D:int=0)<transacts>:int =
    Print("visit {N} {D}")
    if(N>0)then(D | Walk((N-1,C)))else D
Pair(N:int,C:counter)<transacts>:tuple(int,counter) =
    Note(40,C)
    (N,C)
Both(N:int,C:counter,?D:int=0)<transacts>:int = D | Note(N,C)
Main()<transacts>:void =
    C:=counter{}
    P:tuple(int,counter)=(2,C)
    for(V:=Walk(P,?D:=Note(20,C))){Print("all {V} {C.N}")}
    if(V:=Walk(Pair(1,C),?D:=Note(30,C)),V=0)then Print("first {V} {C.N}")
    for(V:=Both((3,C),?D:=Note(10,C))){Print("inline {V} {C.N}")}
