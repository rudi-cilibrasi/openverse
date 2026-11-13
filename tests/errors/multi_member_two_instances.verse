# expect: 8:17: expected int, found string (Two is taken with T, at one instance of its type parameters for a whole search: a call of it at another is not supported yet, #283)
# (#283) A generic function with several values that a recursive one's code
# calls is taken with it at one instance of its type parameters for a whole
# search, as a generic group's own functions are.
Two(X:t, Y:t where t:type)<transacts>:t = X | Y
T(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        S := Two("a", "bb")
        T(N - 1) + Two(N, 10) + S.Length
Main()<transacts>:void =
    for (V := T(1)) { Print("v {V}") }
