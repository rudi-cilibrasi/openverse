# A tuple compared with an array of the same elements, and a tuple passed
# where an array is expected.
# Tests LANGUAGE.md, Types: "a tuple converts to an array of its elements
# where an array is expected, and compares with an array as one
# (array{1,2} = (1,2))"; Equality and the empty value: "a tuple and the
# array of its elements" are one value. Epic's compiler may refuse either.
# OpenVerse prints (Lean and C agree):
#   eq y n total 15
Total(A:[]int):int =
    var S:int = 0
    for (X : A):
        set S += X
    S

Main():void =
    P := if (array{1, 2} = (1, 2)) then "y" else "n"
    Q := if ((1, 2) = array{2, 1}) then "y" else "n"
    Print("OVPROBE eq {P} {Q} total {Total((4, 5, 6))}")
