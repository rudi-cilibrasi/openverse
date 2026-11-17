varcell:=class{var VCell:int=0}
F(H:varcell,N:int)<computes>:int=
    var Seen:int=0
    for(I:=1..N):
        set Seen+=I
        set H.VCell+=I
        if(I=2):return Seen|Seen+1
    Seen|Seen+1
Main():void={}
