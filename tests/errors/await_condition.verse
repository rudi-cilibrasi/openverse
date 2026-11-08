# expect: Await suspends, and a failure context
W()<suspends>:void = Sleep(1.0)
Main()<suspends>:void =
    T := spawn{W()}
    if (T.Await() = 1) then Print("x")
