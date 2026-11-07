# expect: 3:8: '=' compares values of different types, int and float
Main():void =
    if (0 = 0.0) then Print("x")
