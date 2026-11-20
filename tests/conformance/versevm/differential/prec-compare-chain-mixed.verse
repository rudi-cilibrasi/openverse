# Comparison chains (#724): which operand a comparison yields and how a
# chain groups, asked with mixed directions and with values. A chain of the
# form X < Y > Z is left out: Epic's parser reads `< Y >` as brackets (3100,
# S77).
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
