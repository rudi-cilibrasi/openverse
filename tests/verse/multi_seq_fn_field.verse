# (#283) Choice points in sequence: a choice after its call of itself, in a <computes> function that prints (a function in a field): taken lazily.
Loud(N:int)<computes>:int =
    Print("loud {N}")
    N
holder := class:
    Op:type{_(:int)<computes>:int}
other := class:
    Op(N:int)<computes>:int = N
R(H:holder, N:int)<computes><decides>:int =
    N > 0
    H.Op(N) | R[H, N - 1] + (0 | 1)
Main():void = if (X := R[holder{Op := Loud}, 2]) then Print("first {X}")
