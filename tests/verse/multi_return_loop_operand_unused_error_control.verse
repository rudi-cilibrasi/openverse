F(N:int)<computes>:int=
    if(N>=2):return 2|Err()
    N|N+1
Main():void=
    if(V:=F(3),V=2)then Print("first3 {V}")else Print("bad")
    if(V:=F(1),V=1)then Print("first1 {V}")else Print("bad")
    Print("after")
