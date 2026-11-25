# Comparison chains (#724): which operand a comparison yields and how a
# chain groups, asked with mixed directions and with values. A chain of the
# form X < Y > Z is left out: Epic's parser reads `< Y >` as brackets (3100,
# S77).
# OpenVerse printed, until Epic's result below (every adjacent pair):
#   mixed y n n y y y y y | values 2 5 2 9 2 2 2 9 | grouped 2 2 n y
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-20) printed
#   mixed n n n n y n n y | values 2 5 2 9 2 2 2 -1 | grouped 2 2 n y
# A chain in one direction checks every adjacent pair (3 < 5 < 4 and
# 5 > 3 > 4 fail); < or <= after > or >= compares the left operand of what
# is before it, (9 > 1) < 5 being 9 < 5. OpenVerse now prints it too (#724,
# Lean and C agreeing).
Main():void =
    A := if (5 > 1 < 3) then "y" else "n"
    C := if (3 < 5 < 4) then "y" else "n"
    D := if (5 > 3 > 4) then "y" else "n"
    F := if (3 > 1 < 2) then "y" else "n"
    H := if (4 >= 4 < 5) then "y" else "n"
    I := if (3 > 1 <= 1) then "y" else "n"
    J := if (9 > 1 < 5) then "y" else "n"
    K := if (2 > 1 < 5) then "y" else "n"
    Print("OVPROBE mixed {A} {C} {D} {F} {H} {I} {J} {K}")
    V1 := if (W := (2 < 5)) then W else -1
    V2 := if (W := (5 > 2)) then W else -1
    V3 := if (W := (2 < 5 < 9)) then W else -1
    V4 := if (W := (9 > 5 > 2)) then W else -1
    V5 := if (W := (2 <= 2)) then W else -1
    V6 := if (W := (2 = 2)) then W else -1
    V7 := if (W := (2 <> 3)) then W else -1
    V8 := if (W := (9 > 1 < 5)) then W else -1
    Print("OVPROBE values {V1} {V2} {V3} {V4} {V5} {V6} {V7} {V8}")
    P1 := if (W := ((2 < 5) < 9)) then W else -1
    P2 := if (W := (2 < (5 < 9))) then W else -1
    P3 := if ((5 > 1) < 3) then "y" else "n"
    P4 := if (5 > (1 < 3)) then "y" else "n"
    Print("OVPROBE grouped {P1} {P2} {P3} {P4}")
