# Comparison chains: a < b < c checks every adjacent pair, and <> is left
# associative.
# Tests LANGUAGE.md, Readings, "Associativity of comparisons": "chains:
# every adjacent pair checked, each operand evaluated once, result is the
# leftmost" and Operators: "<> is left-associative: 1 <> 2 <> 1 is (1 <> 2)
# <> 1, which fails, as the Book's tests have it, Associativity.versetest:6-9"
# (the Book's prose: chains check all adjacent pairs). Left associativity for
# < would give y for 3 < 5 < 4; a chain for <> would give y for 1 <> 2 <> 1.
# Each letter: y the comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   y n y y ne n y value 2
Main():void =
    A := if (1 < 2 < 3) then "y" else "n"
    B := if (3 < 5 < 4) then "y" else "n"
    C := if (5 > 1 < 3) then "y" else "n"
    D := if (1 <= 1 <= 2 < 3) then "y" else "n"
    E := if (1 <> 2 <> 1) then "y" else "n"
    F := if (1 <> 2 <> 3) then "y" else "n"
    V := if (W := (2 < 5 < 9)) then W else -1
    Print("OVPROBE {A} {B} {C} {D} ne {E} {F} value {V}")
