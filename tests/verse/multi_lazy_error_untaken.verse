# a value that would overflow, after the one an if takes: never computed (#246)
Big(N:int)<computes><decides>:int = N | N * 4611686018427387904 | Big[N - 1]
Main():void =
    if (X := Big[3]):
        Print("{X}")
