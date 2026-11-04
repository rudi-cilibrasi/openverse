# expect: does not allow shadowing
Main():void =
    X := 1
    if (X > 0):
        X := 2
