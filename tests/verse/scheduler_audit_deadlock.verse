# With no possible local wake, the command-line reference scheduler errors.
Main()<suspends>:void=
    Print("waiting")
    Sleep(Inf)
    Print("after")
