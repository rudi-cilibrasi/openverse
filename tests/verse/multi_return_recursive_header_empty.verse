Cell:=class{var N:int=0}
Count(S:Cell,N:int)<transacts>:int=
    set S.N+=1
    if(N=0)then 0|100 else N|Count(S,N-1)
Prefix(S:Cell)<transacts>:int=
    set S.N+=100
    S.N
Pick(S:Cell)<transacts>:int=
    for(P:=Prefix(S), V:=Count(S,3), V>P):
        Y:=V|V+100
        if(V=1):return Y
        Print("advance {Y}")
    S.N|S.N+10
Main()<transacts>:void=
    S:=Cell{}
    for(V:=Pick(S)):Print("{V}")
    Print("state {S.N}")
