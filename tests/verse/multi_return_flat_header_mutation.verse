Pick(Limit:int)<transacts>:int=
    var N:int=0
    for(A:=1|2,A<=Limit):
        set N+=1
        Y:=N|N+10
        if(A=2):return Y
        Print("advance {A} {Y}")
    N
Main()<transacts>:void=
    for(V:=Pick(2)):Print("all {V}")
    for(V:=Pick(1)):Print("fallback {V}")
    if(V:=Pick(2),V=13)then Print("first {V}")else Print("missed")
