Cell:=class{var N:int=0}
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Pick(S:Cell,N:int)<transacts>:int=
    for(V:=if(N>0)then Pick(S,N-1) else 1):
        Y:=V|V+100
        defer:Cleanup(S,V,Y)
        if(V=1):return Y|Y+1000
        Print("advance {V} {Y} {S.N}")
    S.N
Main()<transacts>:void=
    S0:=Cell{}
    for(V:=Pick(S0,1)):Print("all {V}")
    Print("state {S0.N}")
    F0:=Cell{}
    if(V:=Pick(F0,1),V=101)then Print("first {V}")else Print("missed")
    Print("state {F0.N}")
    R0:=Cell{}
    if(V:=Pick(R0,1),V=9999)then Print("bad")else Print("reject {R0.N}")
