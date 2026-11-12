# (#283) Choice points in sequence: a call of itself followed by a choice.
# The code after the call (here a Print) runs once on each of the call's
# values, then the choice gives its values for each. In a for, what that code
# did stays once the choice is reached, even when the filter rejects every
# value after it; where the first success is taken it is undone with the path
# that leads to no success (the function prints, so it is compiled as
# functions of its own there, one per continuation member).
T(N:int)<transacts><decides>:int =
    N > 0
    X := T[N - 1] | N
    Print("t {N} {X}")
    X | X + 100
P(N:int)<transacts><decides>:int =
    N > 0
    X := P[N - 1] | N
    X | X + 100
Main()<transacts>:void =
    for (V := T[2]) { Print("v {V}") }
    Print("--")
    for (V := T[2], V > 100) { Print("v {V}") }
    Print("--")
    if (V := T[2], V > 100) then Print("first {V}")
    if (V := T[2], V > 300) then Print("first {V}") else Print("none")
    # (with no effects, the lazy loop itself where the first success is taken)
    if (V := P[3], V > 200) then Print("first {V}")
