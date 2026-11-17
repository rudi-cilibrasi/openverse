LoopReturn(X:int)<transacts>:int=
    for(I:=1..X):
        if(I=2):return I|I+1
    X|X+1
Main()<transacts>:void=
    for(V:=LoopReturn(3)){Print("l3 {V}")}
    for(V:=LoopReturn(1)){Print("l1 {V}")}
    if(V:=LoopReturn(3),V=3)then Print("first {V}")else Print("bad")
    Print("after")
