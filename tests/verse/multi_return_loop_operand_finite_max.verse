F(L:int,H:int)<computes>:int=
    for(I:=L..H):
        if(I=0):return 5|6
    7|8
Main():void=
    for(V:=F(9223372036854775807,9223372036854775807)){Print("max {V}")}
    for(V:=F(2,1)){Print("empty {V}")}
    for(V:=F(0,0)){Print("stop {V}")}
    if(V:=F(9223372036854775807,9223372036854775807),V=8)then Print("first {V}")else Print("bad")
    Print("after")
