# expect: 10:0: R has several values and is recursive, or called by a recursive one, and it may print (Loud does)
# (its call of itself inside an alternative: all its values computed at a call, F$all, not taken lazily, #246)
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
