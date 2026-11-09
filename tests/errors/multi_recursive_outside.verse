# expect: 6:13: Down has several values, so a call of it must be in a failure context that takes them
Down(N:int)<computes><decides>:int =
    N >= 0
    N | Down[N - 1]
Main():void =
    X := Down[1]
    Print("{X}")
