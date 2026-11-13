# (#283) A generic function with several values that a recursive one's code
# calls at two instances of its type parameters in one search: the call at
# the second is a call of a copy of it of its own, another member of the
# machine, at that instance.
Two(X:t, Y:t where t:type)<transacts>:t = X | Y
T(N:int)<transacts>:int =
    if (N <= 0) then 0 else:
        S := Two("a", "bb")
        T(N - 1) + Two(N, 10) + S.Length
Main()<transacts>:void =
    for (V := T(1)) { Print("v {V}") }
