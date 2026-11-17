F(N:int)<transacts>:int=
    var Seen:int=if(N=0)then(return 90)else 1
    defer:
        set Seen+=100
        Print("out {Seen}")
    if(N>=1):
        defer:
            set Seen+=10
            Print("row 1 {Seen}")
        set Seen+=1
    if(N>=2):
        defer:
            set Seen+=10
            Print("row 2 {Seen}")
        set Seen+=2
        return Seen|Seen+1
    Seen|Seen+1
Main()<transacts>:void=
    for(V:=F(0)){Print("early {V}")}
    for(V:=F(3)){Print("all3 {V}")}
    for(V:=F(1)){Print("all1 {V}")}
    Print("after")
