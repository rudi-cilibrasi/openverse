# expect: 6:0: D has several values and a defer:, and is recursive or called by a recursive one (so its values are computed at the call, or taken lazily): not supported yet (#235, #283)
# (#283) A function with several values that a recursive one's code calls is
# taken by that one's machine, where its defer: would run once for the
# machine's code, not as each value leaves it: refused, as a recursive
# one's is.
D(N:int)<transacts>:int =
    defer:
        Print("d")
    N | -N
T(N:int)<transacts>:int = if (N <= 0) then 0 else T(N - 1) + D(N)
Main()<transacts>:void =
    for (V := T(2)) { Print("v {V}") }
