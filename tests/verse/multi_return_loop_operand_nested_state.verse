F(N:int)<transacts>:int=
    var I:int=0
    var Seen:int=1
    defer:
        set Seen+=100
        Print("out {Seen}")
    loop:
        set I+=1
        defer:
            set Seen+=10
            Print("outer {I} {Seen}")
        var J:int=0
        loop:
            set J+=1
            defer:
                set Seen+=2
                Print("inner {I} {J} {Seen}")
            set Seen+=J
            if(I=2,J=2):return Seen|Seen+1
            if(J=2):break
        if(I>=N):break
    Seen|Seen+1
Main()<transacts>:void=
    for(V:=F(3)){Print("v {V}")}
    for(V:=F(1)){Print("one {V}")}
    if(V:=F(3),V=24)then Print("first {V}")else Print("bad")
    if(V:=F(3),V=999)then Print("bad")else Print("none")
