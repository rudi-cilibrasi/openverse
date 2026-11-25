# Equality of rationals in lowest terms, and of a rational with an int.
# Tests LANGUAGE.md, rational: "= and <> compare rationals in lowest terms
# (6 / 4 = 3 / 2)"; "int is a subtype of rational: an int passes as one";
# Equality and the empty value: two values of different types are equal
# only when they are one value, "an int and the rational it is". Each
# letter: y the comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   eq y y y y n | int y y 5 3
Half(X:int)<computes><decides>:rational = X / 2

Main():void =
    if (R := 6 / 4, S := 3 / 2, T := -1 / 2, U := 1 / -2, V := 4 / 2, W := 1 / 3, X := 2 / 7):
        A := if (R = S) then "y" else "n"
        B := if (T = U) then "y" else "n"
        C := if (V = 2) then "y" else "n"
        D := if (W <> X) then "y" else "n"
        E := if (W = X) then "y" else "n"
        Print("OVPROBE eq {A} {B} {C} {D} {E}")
    if (H := Half[6]):
        F := if (H = 3) then "y" else "n"
        G:rational = 5
        I := if (G = 10 / 2) then "y" else "n"
        Print("OVPROBE int {F} {I} {Floor(G)} {Ceil(H)}")
