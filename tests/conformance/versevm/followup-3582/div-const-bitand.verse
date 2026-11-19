# 3582 follow-up (#724), compile only: a module constant defined by a call
# of BitAnd, an intrinsic the Book's Runtime API reference declares
# <converges>. OpenVerse admits it and prints "mask 2".
Mask:int = BitAnd(6, 3)

Main():void =
    Print("OVPROBE mask {Mask}")
