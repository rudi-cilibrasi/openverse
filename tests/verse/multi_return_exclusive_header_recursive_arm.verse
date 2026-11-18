Cell:=class{var N:int=0}
Choose(S:Cell,Pass:logic)<transacts><decides>:void=
    set S.N+=1000
    Pass?
Count(S:Cell,N:int)<transacts>:int=
    set S.N+=1
    if(N=0)then 0|100 else N|Count(S,N-1)
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Pick(S:Cell,Pass:logic)<transacts>:int=
    for(V:=if(Choose[S,Pass])then Count(S,3) else (4|1),V<>2):
        Y:=V|V+100
        defer:Cleanup(S,V,Y)
        if(V=1):return Y|Y+1000
        Print("advance {V} {Y} {S.N}")
    S.N
Main()<transacts>:void=
    S:=Cell{}
    for(V:=Pick(S,true)):Print("all {V}")
    Print("state {S.N}")
    First:=Cell{}
    if(V:=Pick(First,false),V=101)then Print("first {V}")else Print("missed")
    Print("state {First.N}")
    Reject:=Cell{}
    if(V:=Pick(Reject,true),V=9999)then Print("bad")else Print("reject {Reject.N}")
