# expect: which has the effect <reads>, which its effects (<computes>) do not allow
base := class:
    var Count:int=0
    Read()<reads>:int = Count
child := class(base):
    Read<override>()<computes>:int = (super:)Read()|2
Main():void=for(V:=child{}.Read()):Print("{V}")
