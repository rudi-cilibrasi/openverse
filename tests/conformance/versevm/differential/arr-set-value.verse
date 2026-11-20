# The value of a set expression, of an array element and of a variable,
# used as a value in a condition.
# Tests LANGUAGE.md, Supported, Mutation: "set A[i] = e (fails out of range;
# returns e)"; the Book (01_expressions.md:994): a set "returns the value
# being assigned". Epic's compiler may give a set no value it can bind.
# OpenVerse prints (Lean and C agree):
#   value 7 5 5 | compound 8 8
Main():void =
    var A:[]int = array{1, 2, 3}
    var X:int = 0
    if (V := (set A[0] = 7), W := (set X = 5)):
        Print("OVPROBE value {V} {W} {X}")
    U := (set X += 3)
    Print("OVPROBE compound {U} {X}")
