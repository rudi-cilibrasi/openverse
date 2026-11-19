# a value that would overflow, after the one an if takes: never computed (#246)
# (the overflow: ToString of an int beyond 64 bits, #724)
Big(N:int)<computes><decides>:int = N | ToString(N * 4611686018427387904).Length | Big[N - 1]
Main():void =
    if (X := Big[3]):
        Print("{X}")
