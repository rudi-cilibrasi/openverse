# Equality of options: full against full, full against empty, empty
# against false, and nested.
# Tests LANGUAGE.md, Equality and the empty value: "the empty option" is
# one value with false; Operators: = by value. Each letter: y the comparison
# succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   y y n y n y
Main():void =
    A:?int = option{1}
    B:?int = option{1}
    C:?int = option{2}
    E:?int = false
    P := if (A = B) then "y" else "n"
    Q := if (A <> C) then "y" else "n"
    R := if (A = E) then "y" else "n"
    S := if (E = false) then "y" else "n"
    N1:??int = option{E}
    N2:??int = false
    T := if (N1 = N2) then "y" else "n"
    U := if (option{option{1}} = option{A}) then "y" else "n"
    Print("OVPROBE {P} {Q} {R} {S} {T} {U}")
