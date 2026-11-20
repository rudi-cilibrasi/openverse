# Quotient and Mod of every sign combination, inside 64 bits.
# Tests LANGUAGE.md, Built-ins: "Quotient[X, Y], Mod[X, Y] (Euclidean)";
# Epic's digest: "Quotient[X/Y] = Floor[X/Y] when Y > 0, Ceil[X/Y] when
# Y < 0", "0 <= Mod[X,Y] < Abs(Y)". Truncating division (C's) would give
# q -3 and m -1 for -7, 2.
# OpenVerse prints (Lean and C agree):
#   quotient 3 -4 -3 4 | mod 1 1 1 1 | exact -2 0 0 999999 | zero fails fails
Main():void =
    if (A := Quotient[7, 2], B := Quotient[-7, 2], C := Quotient[7, -2], D := Quotient[-7, -2]):
        Print("OVPROBE quotient {A} {B} {C} {D}")
    if (A := Mod[7, 2], B := Mod[-7, 2], C := Mod[7, -2], D := Mod[-7, -2]):
        Print("OVPROBE mod {A} {B} {C} {D}")
    if (A := Quotient[-6, 3], B := Mod[-6, 3], C := Quotient[0, -4], D := Mod[-1, 1000000]):
        Print("OVPROBE exact {A} {B} {C} {D}")
    Z:int = 0
    E := if (Quotient[5, Z]) then "ok" else "fails"
    F := if (Mod[5, Z]) then "ok" else "fails"
    Print("OVPROBE zero {E} {F}")
