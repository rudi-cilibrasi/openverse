F(N:int)<transacts>:int=
    if(N>0)then block:
        var Seen:int=0
        defer:
            set Seen+=10
            Print("cleanup {Seen}")
        if(N>=2):return Seen|Seen+1
        Seen|Seen+1
    else block:
        Seen:=7
        Seen|Seen+1
Main()<transacts>:void=
    for(V:=F(0)){Print("other {V}")}
    for(V:=F(3)){Print("loop {V}")}
    if(V:=F(3),V=1)then Print("first {V}")else Print("bad")
    Print("after")
