# Ordering of rationals, and of a rational with an int.
# Tests LANGUAGE.md, Readings, "Ordering of rationals": "not stated (§2 lists
# < ... for int and float)"; openverse: "exact (by continued fractions, so it
# cannot overflow), and an int compares with a rational". Epic's compiler may
# refuse < on rationals: that refusal is the answer. Each letter: y the
# comparison succeeded, n it failed.
# OpenVerse (#724) printed, until Epic's result below:
#   order y y y y y n
# Epic's Verse compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) refuses the program: 3509, "No overload of the function
# `operator'<'` matches the provided arguments (:rational,:rational)". The
# Book declares the relational operators for int and float only, so
# OpenVerse now refuses it too (#724), citing 3509.
Main():void =
    if (A := 1 / 3, B := 1 / 2, C := 7 / 2, D := -5 / 3):
        P := if (A < B) then "y" else "n"
        Q := if (B > A) then "y" else "n"
        R := if (C < 4) then "y" else "n"
        S := if (3 <= C) then "y" else "n"
        T := if (D > -2) then "y" else "n"
        U := if (D >= -1) then "y" else "n"
        Print("OVPROBE order {P} {Q} {R} {S} {T} {U}")
