# A <computes> struct's fields are set through a variable, also inside an
# array; a path that reaches an object reads the plain structs before it and
# writes the object's var field (Book of Verse ch. 5; its tests,
# Mutability.versetest 424-447).
point := struct<computes>{X:int = 0, Y:int = 0}
cell := class{var At:point = point{}}
holder := struct{C:cell = cell{}}
Main():void =
    var P:point = point{}
    set P.X = 3
    var Ps:[]point = array{point{}, point{}}
    if (set Ps[1].Y = 4) {}
    H:holder = holder{}
    set H.C.At.Y = 5
    if (Q := Ps[1]) then Print("{P.X} {Q.Y} {H.C.At.Y}")
