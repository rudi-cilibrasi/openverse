Items(N:int)<computes>:[]int=if(N=0)then array{} else if(N=1)then array{4} else array{4,7,9}
ArrayReturn(N:int)<computes>:[]int=
    for(Item:Items(N)):
        if(Item=7):return array{Item*10,Item*10+1}
    array{99,100}
Main():void=
    for(V:ArrayReturn(3)){Print("hit {V}")}
    for(V:ArrayReturn(1)){Print("miss {V}")}
    for(V:ArrayReturn(0)){Print("empty {V}")}
    if(K:=0|1,V:=ArrayReturn(3)[K],V=71)then Print("first {V}")else Print("bad first")
    if(K:=0|1,V:=ArrayReturn(3)[K],V=99)then Print("bad fallthrough")else Print("no fallthrough")
    if(K:=0|1,V:=ArrayReturn(3)[K],V=900)then Print("bad reject")else Print("none")
    if(V:=option{ArrayReturn(3)[0]}?)then Print("option {V}")else Print("bad option")
    for(V:=first{ArrayReturn(3)[0]}){Print("first block {V}")}
    Print("after")
