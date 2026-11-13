# expect: a defer cannot suspend
Main()<suspends>:void=
    defer:Sleep(0.0)
    Print("end")
