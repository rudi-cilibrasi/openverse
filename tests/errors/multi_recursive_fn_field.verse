# expect: 9:0: R has several values and is recursive, or called by a recursive one, and it may print (Loud does)
Loud(N:int)<computes>:int =
    Print("loud {N}")
    N
holder := class:
    Op:type{_(:int)<computes>:int}
other := class:
    Op(N:int)<computes>:int = N
R(H:holder, N:int)<computes><decides>:int =
    N > 0
    H.Op(N) | R[H, N - 1]
Main():void = if (X := R[holder{Op := Loud}, 2]) then Print("first {X}")
