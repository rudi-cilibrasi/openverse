# A parameter of a function (not a method) is an ordinary argument, not a
# receiver, whatever its name (no parameter can be named Self: it is reserved).
Pair(This:tuple(int,int))<computes>:int=This(0)+This(1)
Single(This:tuple(int))<computes>:int=This(0)
Unit(This:tuple())<computes>:int=7
Id(This:t where t:type)<computes>:t=This
Main():void=
    Print("{Pair(1,2)} {Single(3)} {Unit()}")
    R:tuple(int,int)=Id(4,5)
    Print("{R(0)} {R(1)}")
