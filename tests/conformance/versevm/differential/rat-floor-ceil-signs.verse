# Floor and Ceil of int/int rationals of each sign combination.
# Tests LANGUAGE.md, rational: "X / Y on ints is a rational, and fails when
# Y = 0"; "The reverse needs Floor or Ceil, which never fail on a rational";
# Epic agrees past 64 bits (followup-int/int-rational-big); here the signs
# inside them. Truncating division would give floor -3 for -7/2.
# OpenVerse prints (Lean and C agree):
#   a 3 4 -4 -3 | b -4 -3 3 4 | c 2 -2 0 1
Main():void =
    if (A := Floor(7 / 2), B := Ceil(7 / 2), C := Floor(-7 / 2), D := Ceil(-7 / 2)):
        Print("OVPROBE a {A} {B} {C} {D}")
    if (A := Floor(7 / -2), B := Ceil(7 / -2), C := Floor(-7 / -2), D := Ceil(-7 / -2)):
        Print("OVPROBE b {A} {B} {C} {D}")
    if (A := Floor(6 / 3), B := Ceil(-6 / 3), C := Floor(0 / -5), D := Ceil(1 / 1000)):
        Print("OVPROBE c {A} {B} {C} {D}")
