# Ordering of rationals, and of a rational with an int.
# Tests LANGUAGE.md, Readings, "Ordering of rationals": "not stated (§2 lists
# < ... for int and float)"; openverse: "exact (by continued fractions, so it
# cannot overflow), and an int compares with a rational". Epic's compiler may
# refuse < on rationals: that refusal is the answer. Each letter: y the
# comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   order y y y y y n
Main():void =
    if (A := 1 / 3, B := 1 / 2, C := 7 / 2, D := -5 / 3):
        P := if (A < B) then "y" else "n"
        Q := if (B > A) then "y" else "n"
        R := if (C < 4) then "y" else "n"
        S := if (3 <= C) then "y" else "n"
        T := if (D > -2) then "y" else "n"
        U := if (D >= -1) then "y" else "n"
        Print("OVPROBE order {P} {Q} {R} {S} {T} {U}")
