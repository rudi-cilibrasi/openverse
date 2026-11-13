# expect: defer: is a statement: it has no value
Early()<decides>:void = {}
Run()<decides>:void =
    Early[] and defer{Print("C")}
    Print("D")
Main():void = if (Run[]) {}
