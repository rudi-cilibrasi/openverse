State:=class{var N:int=0}
Sources(S:State,Mode:int)<transacts><decides>:[string]int=
    set S.N+=1
    Print("source {S.N}")
    Mode>=0
    if(Mode=0)then map{}|map{} else map{}|map{"z"=>2,"a"=>3}|map{"b"=>5,"a"=>7}
Row(S:State,K:string,V:int)<transacts>:void=
    set S.N+=10*V
    Print("row {K} {S.N}")
Cleanup(S:State,K:string)<transacts>:void=
    set S.N+=1
    Print("cleanup {K} {S.N}")
Pick(S:State,Need:int,Mode:int)<transacts>:int=
    for(K -> V:Sources[S,Mode]):
        Row(S,K,V)
        defer:Cleanup(S,K)
        if(V=Need):return S.N|block{Print("second {S.N}");S.N+100}
    S.N|S.N+1000
Main()<transacts>:void=
    A:=State{}
    for(V:=Pick(A,7,1)):Print("all {V}")
    Print("state {A.N}")
    B:=State{}
    if(V:=Pick(B,7,1),V>200)then Print("first {V}")else Print("missing")
    Print("state {B.N}")
    C:=State{}
    if(V:=Pick(C,7,1),V=999)then Print("bad")else Print("none {C.N}")
    D:=State{}
    for(V:=Pick(D,999,1)):Print("fallback {V}")
    Print("state {D.N}")
    for(Mode:array{-1,0}):
        E:=State{}
        for(V:=Pick(E,7,Mode)):Print("empty {Mode} {V}")
        Print("state {E.N}")
