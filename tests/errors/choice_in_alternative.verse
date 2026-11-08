# expect: 3:16: a choice (a | b) cannot be taken from here
Main():void =
    if (X := (1 | 2) + 1 | 5) then Print("{X}")
