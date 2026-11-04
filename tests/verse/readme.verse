Half(N:int)<decides>:int =
    Mod[N, 2] = 0
    Quotient[N, 2]

Main():void =
    var Attempts:int = 0
    if (set Attempts += 1, Attempts > 100):   # fails: the write is rolled back
        Print("unreachable")
    Print("Attempts = {Attempts}")            # Attempts = 0
    for (I := 1..6, H := Half[I]) { Print("{I} / 2 = {H}") }
