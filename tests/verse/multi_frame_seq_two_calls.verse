# (#283) Choice points in sequence: two calls of itself in sequence, the
# second on each value of the first, then the code after it on each value of
# the second; in a mutual group too, a call of the other function after a
# call of it.
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
U(N:int)<transacts>:int =
    if (N <= 0) then 0 else (U(N - 1) + Tell("u {N}", U(N - 1)) | N)
Ev(N:int)<transacts>:int = if (N <= 0) then 0 else (Od(N - 1) + Od(N - 1) | N)
Od(N:int)<transacts>:int =
    Print("od {N}")
    if (N <= 0) then 1 else (Ev(N - 1) | 7)
Main()<transacts>:void =
    for (W := U(2)) { Print("w {W}") }
    if (W := U(2), W > 1) then Print("first {W}")
    for (V := Ev(2)) { Print("e {V}") }
    if (V := Ev(2), V > 2) then Print("first {V}")
