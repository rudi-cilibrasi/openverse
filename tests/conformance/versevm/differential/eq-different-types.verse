# Comparisons between values of different types: an int and a float, an
# array and a string, an int and a rational.
# Tests LANGUAGE.md, Readings, "= between different types": "Comparisons
# between different types still compile, but they always fail" (ch. 4);
# Equality: "two values of different types are equal only when they are one
# value: ... an int and the rational it is". Epic's compiler may refuse the
# first two. Each letter: y the comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   n y n rational y
Main():void =
    I:int = 0
    F:float = 0.0
    P := if (I = F) then "y" else "n"
    Q := if (I <> F) then "y" else "n"
    R := if (array{97} = "a") then "y" else "n"
    if (H := 4 / 2):
        S := if (H = 2) then "y" else "n"
        Print("OVPROBE {P} {Q} {R} rational {S}")
