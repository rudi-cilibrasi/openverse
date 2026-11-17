F(N:int)<transacts>:int=
    block:
        var Seen:int=10
        defer:set Seen+=100
        0
    if(N>=2):
        var Seen:int=20
        defer:set Seen+=100
        return Seen|Seen+1
    N|N+1
Main()<transacts>:void=
    for(V:=F(3)):Print("all {V}")
    if(V:=F(3)+1):Print("first {V}")
