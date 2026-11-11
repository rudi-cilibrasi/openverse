# expect: calls base.Read, which has the effect <reads>
base := class:
    var Count:int=0
    Read()<reads>:int = Count
child := class(base):
    Values()<computes>:int = (super:)Read()|2
Main():void=for(V:=child{}.Values()):Print("{V}")
