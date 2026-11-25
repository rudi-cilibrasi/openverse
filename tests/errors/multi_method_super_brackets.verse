# expect: Read is <decides>
base := class:
    Read(N:int)<transacts><decides>:int =
        N>=0
        N
child := class(base):
    Read<override>(N:int)<transacts><decides>:int = (super:)Read(1)|2
Main():void=for(V:=child{}.Read[1]):Print("{V}")
