F(N:int)<computes>:int=
    loop:
        loop:
            return N|N+1
Main()<transacts>:void=
    for(V:=F(2)):Print("all {V}")
    if(V:=F(2),V=3)then Print("first {V}")else Print("bad")
    Print("after")
