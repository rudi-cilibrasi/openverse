# 3582 follow-up (#724): a module constant defined by an archetype
# instantiation whose field default is a literal. Control.
thing := class:
    Size:int = 3

Shared:thing = thing{}

Main():void =
    Print("OVPROBE size {Shared.Size}")
