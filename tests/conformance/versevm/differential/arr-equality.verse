# Equality of arrays: order, length, nesting, and empty arrays.
# Tests LANGUAGE.md, Operators: "= and <> of any two comparable types, by
# value". Each letter: y the comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   y n y y y y
Main():void =
    A:[]int = array{1, 2}
    E:[]int = array{}
    P := if (A = array{1, 2}) then "y" else "n"
    Q := if (A = array{2, 1}) then "y" else "n"
    R := if (A <> array{1, 2, 3}) then "y" else "n"
    S := if (E = array{}) then "y" else "n"
    T := if (array{A, E} = array{array{1, 2}, array{}}) then "y" else "n"
    U := if (array{A} <> array{E}) then "y" else "n"
    Print("OVPROBE {P} {Q} {R} {S} {T} {U}")
