# expect: 6:22: a call of Down, which has several values, cannot be lifted from here, for now (#235)
Down(N:int)<computes><decides>:int =
    N >= 0
    N | Down[N - 1]
Main():void =
    for (X := 7 | Down[1]) { Print("{X}") }
