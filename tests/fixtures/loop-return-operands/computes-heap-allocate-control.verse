cell:=class<allocates>{var N:int=0}
F(H:cell,N:int)<computes>:cell=
    var Seen:cell=H
    if(I:=N,I>0):
        set Seen=H
        if(I=2):return cell{N:=I}|Seen
    Seen|Seen
Main():void={}
