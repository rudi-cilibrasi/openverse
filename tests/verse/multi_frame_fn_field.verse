# (its call of itself with code after it: taken lazily, the code a return frame that runs on each of its values, #283)
Loud(N:int)<computes>:int =
    Print("loud {N}")
    N
holder := class:
    Op:type{_(:int)<computes>:int}
other := class:
    Op(N:int)<computes>:int = N
R(H:holder, N:int)<computes><decides>:int =
    N > 0
    H.Op(N) | R[H, N - 1] + 0
Main():void = if (X := R[holder{Op := Loud}, 2]) then Print("first {X}")
