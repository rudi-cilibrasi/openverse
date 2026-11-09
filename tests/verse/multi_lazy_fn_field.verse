# a value computed through a function field that prints, in an if (#246)
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
