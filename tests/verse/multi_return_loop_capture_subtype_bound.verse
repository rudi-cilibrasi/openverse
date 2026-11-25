Vehicle:=class<computes>{N:int=1}
Car:=class<computes>(Vehicle){}
Cell:=class{var N:int=0}
Choose(S:Cell,Pass:logic)<transacts><decides>:void=
    set S.N+=1000
    Pass?
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Pick(S:Cell,Pass:logic,X:t,U:u where u:subtype(Vehicle),t:subtype(u))<transacts>:int=
    var Steps:int=0
    for(V:=if(Choose[S,Pass])then (3|X.N) else (4|X.N)):
        set Steps+=1
        Y:=V|V+100
        defer:Cleanup(S,V,Y)
        if(V=1):return Y|Y+1000
        Print("advance {V} {Y} {S.N}")
    S.N
Main()<transacts>:void=
    S:=Cell{}
    for(V:=Pick(S,true,Car{},Vehicle{})):Print("all {V}")
    Print("state {S.N}")
