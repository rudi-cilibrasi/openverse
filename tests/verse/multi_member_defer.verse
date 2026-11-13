# (#283) A function with several values that a recursive one's code calls is
# taken by that one's machine; its defer: runs as each of its values leaves
# it, before the code after the call, as where it is inlined.
D(N:int)<transacts>:int =
    defer:
        Print("d")
    N | -N
T(N:int)<transacts>:int = if (N <= 0) then 0 else T(N - 1) + D(N)
Main()<transacts>:void =
    for (V := T(2)) { Print("v {V}") }
