# followup-corners (#724): Three comparison chains with <= and >=, in the
# style of differential/prec-compare-chain-mixed (Epic: a chain in one
# direction checks every adjacent pair; < or <= after > or >= compares the
# left operand of what is before it): 4 >= 4 < 5, 1 <= 1 <= 2 < 3, 5 >= 1 <=
# 3.
# OpenVerse (Lean and C agreeing): ran, ordered y y n (5 >= 1 <= 3 is 5 <=
# 3).
# If Epic prints ordered y y n, OpenVerse agrees. ordered y y y would mean
# >= then <= checks the adjacent pair (1 <= 3), unlike > then <: OpenVerse
# would follow.
# Not yet compiled or run by UEFN.
Main():void =
    A := if (4 >= 4 < 5) then "y" else "n"
    B := if (1 <= 1 <= 2 < 3) then "y" else "n"
    C := if (5 >= 1 <= 3) then "y" else "n"
    Print("OVPROBE ordered {A} {B} {C}")
