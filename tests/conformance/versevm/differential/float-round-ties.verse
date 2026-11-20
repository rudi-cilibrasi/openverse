# Floor, Ceil, Round and Int of floats: signs, halves and the tie rule.
# Tests LANGUAGE.md, float: "Floor[F], Ceil[F], Round[F] (ties to even) and
# Int[F] (towards zero) give an int"; Epic's digest (UEFN 43.12): Round
# "When the fractional part of Val is 0.5, rounds to the nearest even int".
# Half away from zero would give round 3 4 -3 -4 1 -1 for the ties.
# OpenVerse prints (Lean and C agree):
#   round 2 4 -2 -4 0 0 | round near 2 3 -2 2 | floor 2 -3 -2 -1
#   ceil 3 -2 0 3 | int 2 -2 0 9
Main():void =
    if (A := Round[2.5], B := Round[3.5], C := Round[-2.5], D := Round[-3.5], E := Round[0.5], F := Round[-0.5]):
        Print("OVPROBE round {A} {B} {C} {D} {E} {F}")
    if (A := Round[2.4999999], B := Round[2.5000001], C := Round[-1.5], D := Round[1.5]):
        Print("OVPROBE round near {A} {B} {C} {D}")
    if (A := Floor[2.7], B := Floor[-2.7], C := Floor[-2.0], D := Floor[-0.1]):
        Print("OVPROBE floor {A} {B} {C} {D}")
    if (A := Ceil[2.2], B := Ceil[-2.7], C := Ceil[-0.1], D := Ceil[3.0]):
        Print("OVPROBE ceil {A} {B} {C} {D}")
    if (A := Int[2.7], B := Int[-2.7], C := Int[-0.9], D := Int[9.99]):
        Print("OVPROBE int {A} {B} {C} {D}")
