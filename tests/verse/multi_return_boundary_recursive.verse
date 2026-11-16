R(N:int)<transacts>:int=
    for(I:=1..N):
        if(I=2):return I
    if(N>0)then(R(N-1)|N)else(0|1)
Main()<transacts>:void=
    for(V:=R(3)){Print("a {V}")}
    for(V:=R(1)){Print("b {V}")}
    Print("after")
