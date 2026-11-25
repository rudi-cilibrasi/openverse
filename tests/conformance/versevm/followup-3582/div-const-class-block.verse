# 3582 follow-up (#724), compile only: a module constant defined by an
# archetype of a <computes> class whose `block` calls a <computes> function.
# The constant's definition calls nothing itself (an archetype of a
# <computes> class is admitted, div-const-computes-archetype); the block
# runs at the construction. OpenVerse admits it and prints "size 3".
Count()<computes>:int = 3

thing := class<computes>:
    Size:int = 3
    block:
        Count()

Shared:thing = thing{}

Main():void =
    Print("OVPROBE size {Shared.Size}")
