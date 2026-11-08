# expect: 4:8: 'X' is already defined
Main():void =
    X := 1
    if (X := 1 | 2) then Print("x")
