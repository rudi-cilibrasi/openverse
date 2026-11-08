# expect: sync needs at least two arms that can suspend
Main()<suspends>:void =
    sync:
        Sleep(1.0)
        Print("x")
