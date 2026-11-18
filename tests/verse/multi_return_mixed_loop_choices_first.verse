Overflow(N:int)<computes>:int=9223372036854775807+N
Sources()<computes>:[]int=array{}|array{1}|array{Overflow(1)}
Pick()<computes>:int=
    for(I:Sources()):
        Y:=I|Overflow(I)
        return Y
    0
Main():void=
    if(V:=Pick(),V=1)then Print("first {V}")else Print("missed")
