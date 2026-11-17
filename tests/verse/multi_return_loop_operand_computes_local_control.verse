F(N:int)<computes>:int=
    var Seen:int=1
    if(N>=1):set Seen+=1
    if(N>=2):
        set Seen+=2
        return Seen|Seen+1
    Seen|Seen+1
Run()<computes>:[]int=for(V:=F(3)):V
Main():void=for(V:Run()){Print("{V}")}
