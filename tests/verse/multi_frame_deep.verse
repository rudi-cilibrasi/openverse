# (#283) Deep return frames: the continuation is a list, so a value 100,000
# calls deep is given to 100,000 frames without recursion.
Count(N:int)<transacts>:int =
    if (N <= 0) then 0 else (Count(N - 1) + 1 | N)
Main()<transacts>:void =
    var S:int = 0
    var K:int = 0
    for (V := Count(300)):
        set S += V
        set K += 1
    Print("{K} {S}")
    if (V := Count(100000), V = 100000) then Print("deep {V}")
