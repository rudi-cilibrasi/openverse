# a call of a recursive function with several values as a choice's alternative, in a for (#283)
Down(N:int)<computes><decides>:int =
    N >= 0
    N | Down[N - 1]
Main():void =
    for (X := 7 | Down[1]) { Print("{X}") }
