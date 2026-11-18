# expect: 4:22: this call may signal an event (event.Signal) in a failure context, which the no_rollback effect of an event's Signal does not allow (Epic's Verse compiler, UEFN 43.12: error 3512; #515)
F(E:event(int),X:int):int=
    for(I:=1..X):
        defer:E.Signal(I)
        if(I=2):return I
    X|X+1
Main():void=
    E:=event(int){}
    if(V:=F(E,3),V=2)then Print("{V}")
