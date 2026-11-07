# expect: defer: is a statement: it has no value
Main():void =
    X := defer:
        Print("y")
    Print("x")
