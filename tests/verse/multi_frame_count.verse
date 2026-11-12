# (#283) A call of itself inside an expression, in one alternative of a choice
# in a branch: `Count(N - 1) + 1` runs `+ 1` on each value of the call.
Count(N:int)<transacts>:int =
    if (N <= 0) then 0 else (Count(N - 1) + 1 | N)
Path(N:int)<transacts>:string =
    if (N <= 0) then "" else ("{Path(N - 1)}L" | "{Path(N - 1)}R")
Main()<transacts>:void =
    for (V := Count(3)) { Print("v {V}") }
    if (V := Count(3), V > 2) then Print("first {V}")
    for (P := Path(2)) { Print(P) }
    if (P := Path(3), P.Length = 3, P[1] = 'R') then Print("first {P}")
