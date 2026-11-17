F(N:int)<computes>:int=
    for(I:=1..N):return I|I+1
    0|1
Main():void=for(V:=F(1)){Print("{V}")}
