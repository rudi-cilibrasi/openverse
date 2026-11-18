Values(Group:int)<computes>:[]int=
    if(Group=1)then array{10,11} else array{20,21}
Pick()<transacts>:int=
    for(Group:=1|2, I -> V:Values(Group)):
        Y:=V|V+100
        defer:Print("cleanup {Group} {I} {Y}")
        if(I=1):return Y
        Print("advance {Group} {I} {Y}")
    900
Main()<transacts>:void=
    for(V:=Pick()):Print("all {V}")
    if(V:=Pick(),V=111)then Print("first {V}")else Print("missed")
