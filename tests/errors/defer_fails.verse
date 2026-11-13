# expect: this expression can fail, but it is not in a failure context
F()<decides>:void =
    defer:
        1 = 2
    Print("end")
Main():void = Print("x")
