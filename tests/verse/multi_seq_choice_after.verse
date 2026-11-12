# (#283) Choice points in sequence: a choice after its call of itself, the code before it printing: the call's values each go through that code once, then the choice.
S(N:int)<transacts>:int =
    if (N <= 0) then 0 else block:
        X := S(N - 1)
        Print("got {X}")
        X | X + N
Main()<transacts>:void =
    for (V := S(2)) { Print("v {V}") }
