Cell:=class{var N:int=0}
Select(S:Cell,Pass:logic)<transacts>:int=
    if(Pass?):
        set S.N+=1000
        return 1
    3
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Pick(S:Cell,Pass:logic)<transacts>:int=
    for(V:=case(Select(S,Pass)){1=>(3|1),2=>(2|1),_=>(4|1)}):
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
