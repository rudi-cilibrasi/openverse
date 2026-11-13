# (#283) A return in an if after a choice point, in a recursive function with
# several values or in a function its code calls: that if is code after the
# point, a plain if there, its returning branch's value the alternative's.
T(N:int)<transacts>:int =
    if (N <= 0) then 1 else:
        Y := T(N - 1) | N * 10
        if (Y > 15):
            return 0
        Y
Pick(K:int)<transacts>:int =
    Y := K | K + 10
    if (Y > 12):
        return 0
    Y
U(N:int)<transacts>:int =
    if (N <= 0) then 0 else U(N - 1) + Pick(N)
Main()<transacts>:void =
    for (V := T(2)) { Print("t {V}") }
    for (V := U(2)) { Print("u {V}") }
