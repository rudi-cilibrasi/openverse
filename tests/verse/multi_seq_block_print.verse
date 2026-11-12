# (#283) Choice points in sequence: a choice after its call of itself, in a <computes> function that prints (a block: of a class it constructs): taken lazily, as all its values are not computed at the call.
reader := class<computes>:
    block:
        Print("constructed")
    V:int = 7
R(N:int)<computes><decides>:int =
    N > 0
    reader{}.V | R[N - 1] + (0 | 1)
Main():void = if (X := R[2]) then Print("first {X}")
