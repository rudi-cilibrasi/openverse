Cell:=class{var N:int=0}
Count(S:Cell,N:int)<transacts>:int=
    set S.N+=1
    if(N=0)then 0|10 else N|block{Child:=Count(S,N-1); set S.N+=10; Child+100|Child+200}
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Pick(S:Cell)<transacts>:int=
    for(V:=Count(S,3),V<>102,V<>202):
        Y:=V|V+1000
        defer:Cleanup(S,V,Y)
        if(V=201):return Y|Y+10000
        Print("advance {V} {Y} {S.N}")
    S.N
Main()<transacts>:void=
    S:=Cell{}
    for(V:=Pick(S)):Print("all {V}")
    Print("state {S.N}")
    First:=Cell{}
    if(V:=Pick(First),V=1201)then Print("first {V}")else Print("missed")
    Print("state {First.N}")
    Reject:=Cell{}
    if(V:=Pick(Reject),V=9999)then Print("bad")else Print("reject {Reject.N}")
