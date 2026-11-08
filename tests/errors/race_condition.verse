# expect: race suspends, and a failure context
G()<suspends>:int = 1
Main()<suspends>:void =
    if (race{G(); G()} > 0) then Print("x")
