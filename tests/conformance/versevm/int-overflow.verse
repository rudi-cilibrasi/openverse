Next(N:int)<computes>:int = N + 1

Main():void =
    N := Next(9223372036854775807)
    if (N > 9223372036854775807):
        Print("OVPROBE above signed 64-bit max")
    else:
        Print("OVPROBE at or below signed 64-bit max")
