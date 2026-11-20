# Setting a field of a struct held in a var, and of a struct in an array:
# the copy taken before keeps its value.
# Tests LANGUAGE.md, Supported, Structs: "set S.F = e / op= of a
# struct<computes> (ch. 5: "Only structs marked <computes> (pure structs)
# allow field mutation through a variable")". Epic's compiler may refuse
# <computes> on a struct or the set.
# OpenVerse prints (Lean and C agree):
#   5 2 1 0 5 9
spot := struct<computes>:
    X:int = 0
    Y:int = 0

Main():void =
    var S:spot = spot{X := 1}
    Old := S
    set S.X = 5
    set S.Y += 2
    var Row:[]spot = array{S, S}
    if (set Row[1].X = 9) {}
    if (R0 := Row[0], R1 := Row[1]):
        Print("OVPROBE {S.X} {S.Y} {Old.X} {Old.Y} {R0.X} {R1.X}")
