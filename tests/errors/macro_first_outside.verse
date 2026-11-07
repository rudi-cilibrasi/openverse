# expect: this expression can fail, but it is not in a failure context
Main():void =
    Xs := array{1}
    X := first { Xs[3] }
    Print("{X}")
