# recursive functions with several values (#235): a written type for the
# alternatives, converting each value
R(N:int)<computes><decides>:[]int =
    N > 0
    A:[]int = array{} | R[N - 1]
    A
Q(N:int)<computes><decides>:rational =
    N > 0
    X:rational = 1 | Q[N - 1]
    X
Main():void =
    for (X := R[2]) { Print("{X.Length}") }
    for (Y := Q[2]) { Print("{Floor(Y)}") }
