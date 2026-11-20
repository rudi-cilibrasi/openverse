# Short-circuit of or and and, seen through a counter object that each
# operand bumps when it runs (only in contexts that succeed, so nothing is
# rolled back).
# Tests LANGUAGE.md, Readings, "A choice in an operand of and or or": "A or
# B: if (T := A) then T else B"; Failure: "the left of or" is a failure
# context. If or evaluated both operands, the first count would be 2.
# OpenVerse prints (Lean and C agree):
#   or 1 count 1 and count 2 second 2 count 1
counter := class:
    var N:int = 0

Hit(C:counter, V:int)<transacts><decides>:int =
    set C.N += 1
    V > 0

Main():void =
    C1 := counter{}
    X:int = Hit[C1, 1] or Hit[C1, 2] or 3
    C2 := counter{}
    if (Hit[C2, 5] and Hit[C2, 6]) {}
    C3 := counter{}
    Y:int = Hit[C3, -1] or Hit[C3, 2] or 3
    Print("OVPROBE or {X} count {C1.N} and count {C2.N} second {Y} count {C3.N}")
