Seed(Tag:string,N:int)<reads>:int=block{Print(Tag);N}
source:=interface<reads>:
    Value:int=Seed("interface default",3)
base:=class<reads>(source):
    Other:int=Seed("base default",4)
    block:Print("base block")
derived:=class<transacts>(base):
    var Count:int=0
    Tail:int=Seed("derived default",5)
    block:
        set Count=Value+Other+Tail
        Print("derived block {Count}")
packet(t:type):=struct<computes>:
    Value:t
Wrap(X:t where t:type)<computes>:packet(t)=packet(t){Value:=X}
Main():void=
    D:=derived{}
    Print("result {D.Value} {D.Other} {D.Tail} {D.Count}")
    Print("packet {Wrap(9).Value}")
