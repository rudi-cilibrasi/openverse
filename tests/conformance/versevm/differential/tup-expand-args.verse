# A tuple passed where a function takes several parameters expands into
# them; a tuple returned from a function and expanded at a call.
# Tests LANGUAGE.md, Functions: "a tuple argument expands into parameters
# (Describe(MyTuple))".
# OpenVerse prints (Lean and C agree):
#   123 321 5 4
Add3(A:int, B:int, C:int):int = A * 100 + B * 10 + C

Pair():tuple(int, int) = (4, 5)

Swap(A:int, B:int):tuple(int, int) = (B, A)

Main():void =
    T := (1, 2, 3)
    S := Swap(Pair())
    Print("OVPROBE {Add3(T)} {Add3(3, 2, 1)} {S(0)} {S(1)}")
