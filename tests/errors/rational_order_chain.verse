# expect: '<=' does not order a rational
# (#724) in a chain too (differential/rat-ordering).
Main():void =
    if (C := 7 / 2, 3 < 4 <= C):
        Print("less")
