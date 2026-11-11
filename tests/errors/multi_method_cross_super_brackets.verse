# expect: Read is <decides>
base := class:
    Read(N:int)<decides>:int =
        N>=0
        N
child := class(base):
    Values()<transacts>:int = (super:)Read(1)|2
Main():void=for(V:=child{}.Values()):Print("{V}")
