# expect: '>=' does not order a rational: it compares two ints or two floats, and a rational has only = and <> (found int and rational
# (#724) an int with a rational: no overload of two ints or of two floats
# either (differential/rat-ordering's `3 <= C`).
Main():void =
    if (C := 7 / 2, 4 >= C):
        Print("less")
