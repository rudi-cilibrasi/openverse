F(N:int)<computes>:int=
    var Seen:int=1
    defer:set Seen+=100
    for(I:=1..N):
        defer:set Seen+=10
        set Seen+=I
        if(I=2):return Seen|Seen+1
    Seen|Seen+1
Run()<computes>:[]int=for(V:=F(3)):V
Pick()<computes>:int=if(V:=F(3),V=15)then V else -1
Main():void=
    for(V:Run()){Print("all {V}")}
    Print("first {Pick()}")
