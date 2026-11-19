# 3582 follow-up (#724): a module constant defined by a call of a
# constructor function.
thing := class:
    Size:int = 3

MakeThing<constructor>(N:int) := thing:
    Size := N

Shared:thing = MakeThing(4)

Main():void =
    Print("OVPROBE size {Shared.Size}")
