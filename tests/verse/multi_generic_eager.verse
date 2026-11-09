# a generic recursive function with several values computed at the call, F$all, generic too (#235)
Id(Y:t where t:type)<computes>:t = Y
Rep(X:t, N:int where t:type)<computes><decides>:t =
    N > 0
    X | Id(Rep[X, N - 1])
Main():void =
    for (Y := Rep["r", 3]) { Print(Y) }
    if (Y := Rep[7, 2], Y > 5) then Print("first {Y}")
