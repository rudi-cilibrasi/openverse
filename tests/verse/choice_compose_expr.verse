# a choice inside an expression that is a choice's alternative: its values in order, where the first success is taken (#283)
Main():void =
    if (X := (1 | 2) + 1 | 5) then Print("{X}")
