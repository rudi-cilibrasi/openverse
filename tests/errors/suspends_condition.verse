# expect: Get suspends, and a failure context
Get()<suspends>:int = 1
Main()<suspends>:void =
    if (Get() > 0) then Print("x")
