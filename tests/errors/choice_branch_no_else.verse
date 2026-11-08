# expect: 3:32: a choice (a | b) cannot be lifted from here
Main():void =
    if (X := if (1 > 0) then (1 | 2)) then Print("x")
