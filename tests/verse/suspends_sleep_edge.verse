# Sleep: negative and NaN durations return at once; Sleep(Inf) with no other task is a deadlock (#156)
Main()<suspends>:void =
    Print("a")
    Sleep(-1.0)
    Print("b")
    Sleep(0.0 / 0.0)
    Print("c")
    Sleep(Inf)
    Print("never")
