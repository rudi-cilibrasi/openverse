# 3582 follow-up (#724), compile only: a module constant defined by an
# archetype of a <computes> class (no call; the Book's tests construct one
# at module scope, ParametricTypes.versetest:459-468, and refuse a class
# with the transacts effect, 3512, as UEFN 43.12 did in
# div-const-constructor). OpenVerse admits it and prints "x 1".
point := class<computes>:
    X:int = 1

Origin:point = point{}

Main():void =
    Print("OVPROBE x {Origin.X}")
