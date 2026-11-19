# 3582 follow-up (#724), compile only: a field default that reads a field of
# another object, a module constant of a <computes> class (no call).
# OpenVerse admits it and prints "size 4".
point := class<computes>:
    X:int = 4

Origin:point = point{}

thing := class:
    Size:int = Origin.X

Main():void =
    T := thing{}
    Print("OVPROBE size {T.Size}")
