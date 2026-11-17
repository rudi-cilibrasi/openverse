F(N:int)<computes>:int=
    var Seen:int=1
    defer:set Seen+=100
    if(N>=1):
        defer:set Seen+=10
        set Seen+=1
    if(N>=2):
        defer:set Seen+=10
        set Seen+=2
        return Seen|Seen+1
    Seen|Seen+1
Run()<computes>:[]int=for(V:=F(3)):V
Pick()<computes>:int=if(V:=F(3),V=15)then V else -1
Main():void=
    for(V:Run()){Print("all {V}")}
    Print("first {Pick()}")
