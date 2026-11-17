F(N:int)<transacts>:int=
    for(I:=1..2):
        var Seen:int=I*10
        defer:set Seen+=100
        if(I=2):return Seen|Seen+1
    N|N+1
Main()<transacts>:void=
    for(V:=F(3)):Print("all {V}")
    if(V:=F(3)+1):Print("first {V}")
