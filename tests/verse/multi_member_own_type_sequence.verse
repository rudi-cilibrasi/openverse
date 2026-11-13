# (#283) A function with several values that a recursive one's code calls, whose values are of
# another type than the recursive one's, with a choice point after a call in its own code: the
# code after that call gives the callee's values, at their type (before, a type error).
Three(X:string)<transacts>:string =
    Print("three {X}")
    X | X + "!"
Two(X:string, Y:string)<transacts>:string =
    Z := Three(X)
    Z | Y
T(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        S := Two("a", "bbbb")
        T(N - 1) + S.Length
Main()<transacts>:void =
    for (V := T(1)) { Print("v {V}") }
    if (V := T(1), V > 3) then Print("first {V}")
