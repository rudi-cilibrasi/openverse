# expect: 4:22: this call may signal an event (event.Signal) in a failure context, which --signal-no-rollback refuses: the published Verse API makes an event's Signal <no_rollback> (#515)
F(E:event(int),X:int)<transacts>:int=
    for(I:=1..X):
        defer:E.Signal(I)
        if(I=2):return I
    X|X+1
Main():void=
    E:=event(int){}
    if(V:=F(E,3),V=2)then Print("{V}")
