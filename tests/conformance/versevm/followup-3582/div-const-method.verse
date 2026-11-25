# 3582 follow-up (#724): a module constant defined by a method call on
# another module constant.
thing := class:
    Size:int = 3
    Double()<computes>:int = Size * 2

Shared:thing = thing{}
Twice:int = Shared.Double()

Main():void =
    Print("OVPROBE twice {Twice}")
