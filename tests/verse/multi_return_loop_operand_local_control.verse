F(X:int)<transacts>:int=
    var Seen:int=0
    defer:
        set Seen+=100
        Print("out {Seen}")
    if(X>=1):
        defer:
            set Seen+=10
            Print("row 1 {Seen}")
        set Seen+=1
    if(X>=2):
        defer:
            set Seen+=10
            Print("row 2 {Seen}")
        set Seen+=2
        return Seen|Seen+1
    Seen|Seen+1
G(X:int)<transacts>:int=
    for(V:=F(X)):return V+100
    999
Main()<transacts>:void=
    for(V:=F(3)){Print("all3 {V}")}
    for(V:=F(1)){Print("all1 {V}")}
    for(V:=F(0)){Print("all0 {V}")}
    if(V:=F(3),V=14)then Print("first3 {V}")else Print("bad")
    if(V:=F(1),V=12)then Print("first1 {V}")else Print("bad")
    if(V:=F(3),V=99)then Print("bad")else Print("none")
    Print("caller {G(3)}")
    Print("after")
