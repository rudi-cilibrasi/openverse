Count(N:int)<computes>:int=
    if(N=1)then (N+9223372036854775807)|0 else N|(Count(N-1)+100)
Pick():int=
    for(V:=Count(3)):
        Y:=V|V+500
        if(V=3):return Y|Y+1000
        Print("unused {V} {Y}")
    0
Main():void=
    if(V:=Pick(),V=3)then Print("first {V}")else Print("missed")
