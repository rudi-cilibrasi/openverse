# Known finite-duration cutoff, distinguished from an ordinary large timer.
Main()<suspends>:void=
    Sleep(999999999999999.0)
    Print("below cutoff")
    Sleep(1000000000000000.0)
    Print("above cutoff")
