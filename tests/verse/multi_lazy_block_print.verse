# a recursive function with several values, taken lazily in an if (#246): its first value constructs a class whose block: prints
reader := class:
    block:
        Print("constructed")
    V:int = 7
R(N:int)<computes><decides>:int =
    N > 0
    reader{}.V | R[N - 1]
Main():void = if (X := R[2]) then Print("first {X}")
