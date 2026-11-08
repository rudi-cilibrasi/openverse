# expect: 4:14: a choice (a | b) can only be the value of a binding
Main():void =
    X := 1
    if (X = 1 | 2) then Print("x")
