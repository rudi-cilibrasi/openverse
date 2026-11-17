F(N:int)<transacts>:int=
    var Seen:int=0
    defer:
        set Seen+=100
        Print("out {Seen}")
    for(I:=1..1):
        set Seen+=1
        if(N=0):return Seen|Seen+1
    for(J:=1..2):
        set Seen+=10
        if(J=2):return Seen|Seen+1
    Seen|Seen+1
Main()<transacts>:void=
    for(V:=F(0)):Print("zero {V}")
    for(V:=F(1)):Print("one {V}")
    if(V:=F(1),V=22)then Print("first {V}")else Print("bad")
