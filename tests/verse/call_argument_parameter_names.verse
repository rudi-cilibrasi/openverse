# A source parameter named Self is an ordinary argument, not a receiver.
Pair(Self:tuple(int,int))<computes>:int=Self(0)+Self(1)
Single(Self:tuple(int))<computes>:int=Self(0)
Unit(Self:tuple())<computes>:int=7
Id(Self:t where t:type)<computes>:t=Self
Main():void=
    Print("{Pair(1,2)} {Single(3)} {Unit()}")
    R:tuple(int,int)=Id(4,5)
    Print("{R(0)} {R(1)}")
