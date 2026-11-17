F(N:int)<transacts>:int=
    var Seen:int=1
    defer:
        set Seen+=100
        Print("out {Seen}")
    for(I:=1..N):
        defer:
            set Seen+=10
            Print("outer {I} {Seen}")
        for(J:=1..2):
            defer:
                set Seen+=2
                Print("inner {I} {J} {Seen}")
            set Seen+=J
            if(I=2,J=2):return Seen|Seen+1
    Seen|Seen+1
Main()<transacts>:void=
    for(V:=F(3)){Print("v {V}")}
    for(V:=F(1)){Print("one {V}")}
    if(V:=F(3),V=24)then Print("first {V}")else Print("bad")
    if(V:=F(3),V=999)then Print("bad")else Print("none")
