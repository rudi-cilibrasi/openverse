F(E:event(int),N:int)<transacts>:int=
    for(I:=1..N):
        if(I=2):return block{E.Signal(I);I|I+1}
    N|N+1
Main():void=
    E:=event(int){}
    for(V:=F(E,3)){Print("value {V}")}
    Print("after")
