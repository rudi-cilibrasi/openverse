# expect: 6:23: a choice (a | b) cannot be taken from here: not from inside a block, a branch, a struct construction
pt := struct:
    X:int = 0
Main():void =
    # (a struct's fields are evaluated in declaration order, not written order)
    if (P := pt{X := 1 | 2}) then Print("{P.X}")
