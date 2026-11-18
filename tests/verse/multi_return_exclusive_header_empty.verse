Cell:=class{var N:int=0}
Choose(S:Cell,Pass:logic)<transacts><decides>:void=
    set S.N+=1000
    Pass?
Pick(S:Cell,Pass:logic)<transacts>:int=
    for(V:=if(Choose[S,Pass])then (3|1) else (4|1),V>1000):
        Y:=V|V+100
        if(V=1):return Y
        Print("unused {Y}")
    S.N|S.N+1
Main()<transacts>:void=
    S:=Cell{}
    for(V:=Pick(S,true)):Print("{V}")
    Print("state {S.N}")
    F:=Cell{}
    for(V:=Pick(F,false)):Print("{V}")
    Print("state {F.N}")
