# Objects are references: a var field set through one name is seen through
# another, through an array holding the object, and after a function call.
# Tests LANGUAGE.md, Supported, Classes: "var fields"; Mutation: "set S.F.G =
# e" on an object.
# OpenVerse prints (Lean and C agree):
#   108 108 108 0
cell := class:
    var V:int = 0

Bump(C:cell)<transacts>:void =
    set C.V += 5

Main():void =
    A := cell{}
    B := A
    Cells:[]cell = array{A, cell{}}
    set B.V = 3
    Bump(A)
    if (C0 := Cells[0], C1 := Cells[1]):
        set C0.V += 100
        Print("OVPROBE {A.V} {B.V} {C0.V} {C1.V}")
