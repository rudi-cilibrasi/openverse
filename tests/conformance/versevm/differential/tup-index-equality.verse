# Tuples: element access, nesting, and equality of tuples.
# Tests LANGUAGE.md, Types: "tuple(...)"; Operators: "= and <> of any two
# comparable types, by value". Each letter: y the comparison succeeded, n it
# failed.
# OpenVerse prints (Lean and C agree):
#   access 1 a 2.500000 7 a | eq y n y y
Main():void =
    T:tuple(int, string, float) = (1, "a", 2.5)
    N := (T, (7, 8))
    Print("OVPROBE access {T(0)} {T(1)} {T(2)} {N(1)(0)} {N(0)(1)}")
    P := if ((1, 2) = (1, 2)) then "y" else "n"
    Q := if ((1, 2) = (2, 1)) then "y" else "n"
    R := if ((1, (2, "x")) = (1, (2, "x"))) then "y" else "n"
    S := if ((1, "a") <> (1, "b")) then "y" else "n"
    Print("OVPROBE eq {P} {Q} {R} {S}")
