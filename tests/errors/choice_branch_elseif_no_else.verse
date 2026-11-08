# expect: 3:33: a choice (a | b) cannot be lifted from here
Main():void =
    for (X := if (1 > 2) then (1 | 2) else if (1 > 0) then 3) { Print("x") }
