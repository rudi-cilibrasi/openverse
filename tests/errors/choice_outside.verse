# expect: 3:11: a choice (a | b) has several values, so it must be in a failure context that takes them
Main():void =
    X := 1 | 2
    Print("{X}")
