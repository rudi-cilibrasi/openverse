# Integer division by zero fails, in a condition and with or.
# Tests LANGUAGE.md, rational: "X / Y on ints is a rational, and fails when
# Y = 0"; Built-ins: "Floor(X / Y) fails when Y = 0, as X / Y does".
# OpenVerse prints (Lean and C agree):
#   failed failed -1 4
Main():void =
    Z:int = 0
    A := if (R := 5 / Z) then "divided" else "failed"
    B := if (F := Floor(5 / Z)) then "floored" else "failed"
    C:int = Floor(0 / Z) or -1
    D:int = Ceil(7 / 2) or -1
    Print("OVPROBE {A} {B} {C} {D}")
