cell:=class{var N:int=0}
F(H:cell,N:int)<computes>:int=
    var Seen:int=0
    if(I:=N,I>0):
        set Seen+=I
        if(I=2):return H.N|Seen
    Seen|Seen+1
Main():void={}
