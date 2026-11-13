# (#283) A choice with a call of the recursive function as one alternative,
# as a set's value (`=`, or `+=` with its old value read after the choice)
# or a var's initial value: bound first, as such a choice anywhere, so each of
# its values goes to the code after it, as `X := 10 + (T(N - 1) | 5)` does.
Add(N:int)<transacts>:int =
    if (N <= 0) then 1 else:
        var K:int = N
        set K += (Add(N - 1) | 5)
        Print("add {N} {K}")
        K
Put(N:int)<transacts>:int =
    if (N <= 0) then 1 else:
        var K:int = N
        set K = (Put(N - 1) | 5)
        Print("put {N} {K}")
        K + N
Init(N:int)<transacts>:int =
    if (N <= 0) then 1 else:
        var K:int = (Init(N - 1) | 5)
        set K += N
        Print("init {N} {K}")
        K
Main()<transacts>:void =
    for (V := Add(2)) { Print("v {V}") }
    if (V := Add(2), V > 7) then Print("taken {V}")
    for (V := Put(2)) { Print("v {V}") }
    if (V := Put(2), V > 7) then Print("taken {V}")
    for (V := Init(2)) { Print("v {V}") }
    if (V := Init(2), V > 7) then Print("taken {V}")
