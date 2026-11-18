Source(A:int)<computes>:[string]int=
    if(A=1)then map{"a"=>1} else map{"b"=>2,"c"=>3}
Pick()<transacts>:int=
    for(A:=1|2,K -> V:Source(A)):
        Y:=V|V+10
        defer:Print("cleanup {K} {Y}")
        if(A=2):return Y
        Print("advance {K} {Y}")
    100
Main()<transacts>:void=
    for(V:=Pick()):Print("all {V}")
    if(V:=Pick(),V=12)then Print("first {V}")else Print("missed")
