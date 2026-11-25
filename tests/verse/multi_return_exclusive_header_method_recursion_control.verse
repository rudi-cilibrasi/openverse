Der:=class{K:int=3}
Cell:=class{var N:int=0}
Choose(S:Cell,Pass:logic)<transacts><decides>:void=
    set S.N+=1000
    Pass?
Cleanup(S:Cell,V:int,Y:int)<transacts>:void=
    set S.N+=10
    Print("cleanup {V} {Y} {S.N}")
Walker:=class:
    Bias:int=0
    Pick(S:Cell,N:int)<transacts>:int=
        var T:int=N
        set T+=Bias
        for(V:=if(Choose[S,true], T>=0, D:=Der[Der{}])then (3|(if(T>0)then Pick(S,T-2) else 1)) else (4|1)):
            Y:=V|V+100
            defer:Cleanup(S,V,Y)
            if(V=1):return Y|Y+1000
            Print("advance {V} {Y} {S.N} {T}")
        for(V:=if(Choose[S,true], N>1, D:=Der[Der{}])then (5|(if(N>2)then Pick(S,N-2) else 1)) else (4|1)):
            Y:=V|V+100
            defer:Cleanup(S,V,Y)
            if(V=1):return Y|Y+1000
            Print("second {V} {Y} {S.N}")
        S.N
Main()<transacts>:void=
    W:=Walker{Bias:=1}
    S0:=Cell{}
    for(V:=W.Pick(S0,1)):Print("all {V}")
    Print("state {S0.N}")
    F0:=Cell{}
    if(V:=W.Pick(F0,1),V=101)then Print("first {V}")else Print("missed")
    Print("state {F0.N}")
