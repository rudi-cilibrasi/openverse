# expect: Await suspends, and a failure context
Main()<suspends>:void =
    E := event(int){}
    if (E.Await() > 0) then Print("x")
