# expect: 7:0: R has several values and is recursive, or called by a recursive one, and it may print (the block: of reader does)
# (a choice after its call of itself: all its values computed at a call, F$all, not taken lazily, #246, #283)
reader := class<computes>:
    block:
        Print("constructed")
    V:int = 7
R(N:int)<computes><decides>:int =
    N > 0
    reader{}.V | R[N - 1] + (0 | 1)
Main():void = if (X := R[2]) then Print("first {X}")
