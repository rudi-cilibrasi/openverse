# expect: 3:11: a choice (a | b) can only be the value of a binding
Main():void =
    X := 1 | 2
    Print("{X}")
