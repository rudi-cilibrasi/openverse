# expect: 5:8: an operand of '=' must be comparable, and any is not
Main():void =
    X:any = 1
    Y:any = 2
    if (X = Y) then Print("x")
