# expect: Sleep suspends, and a defer cannot suspend
Main()<suspends>:void =
    defer:
        Sleep(1.0)
    Print("x")
