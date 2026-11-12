# (its call of itself with code after it: taken lazily, the code a return frame that runs on each of its values, #283)
reader := class<computes>:
    block:
        Print("constructed")
    V:int = 7
R(N:int)<computes><decides>:int =
    N > 0
    reader{}.V | R[N - 1] + 0
Main():void = if (X := R[2]) then Print("first {X}")
