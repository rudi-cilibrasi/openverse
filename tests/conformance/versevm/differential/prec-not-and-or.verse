# Precedence of not, and, or and the comparisons, seen through which of
# several groupings succeeds.
# Tests LANGUAGE.md, Supported, Operators: "not (below the comparisons,
# above and: not X = Y is not (X = Y))", "A and B and C is (A and B) and C";
# the Book's ch. 4 precedence table (and above or). Each letter: y the
# condition succeeded, n it failed. If not bound looser than and, b would be
# y; if or bound tighter than and, a would be n.
# OpenVerse prints (Lean and C agree):
#   a y b n c y d y e y
Main():void =
    T:logic = true
    F:logic = false
    A := if (T? or F? and F?) then "y" else "n"
    B := if (not 1 = 2 and 1 = 2) then "y" else "n"
    C := if (not 1 = 1 or 2 = 2) then "y" else "n"
    D := if (not not 1 = 1) then "y" else "n"
    E := if (F? and F? or T?) then "y" else "n"
    Print("OVPROBE a {A} b {B} c {C} d {D} e {E}")
