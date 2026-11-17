F(N:int)<computes>:int=
    var Seen:int=1
    for(I:=1..N):
        set Seen+=I
        if(I=2):return Seen|Seen+1
    Seen|Seen+1
Run()<computes>:[]int=for(V:=F(3)):V
Main():void=for(V:Run()){Print("{V}")}
