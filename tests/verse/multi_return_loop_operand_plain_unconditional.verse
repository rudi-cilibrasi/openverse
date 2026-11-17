F(N:int)<computes>:int=
    loop:
        return N|N+1
Caller(N:int)<computes>:int=
    for(V:=F(N)):return V+100
    999
Main():void=
    for(V:=F(2)){Print("all {V}")}
    if(V:=F(2),V=3)then Print("first {V}")else Print("bad")
    Print("caller {Caller(2)}")
