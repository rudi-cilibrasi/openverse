cell:=class<allocates>{var N:int=0}
F(H:cell,N:int)<computes>:cell=
    var Seen:cell=H
    for(I:=1..N):
        set Seen=H
        if(I=2):return cell{N:=I}|Seen
    Seen|Seen
Main():void={}
