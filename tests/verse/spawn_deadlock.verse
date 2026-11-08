# awaiting a task that never ends, with nothing else to run: a deadlock (#156)
W()<suspends>:int =
    Sleep(Inf)
    1
Main()<suspends>:void =
    T := spawn{W()}
    Print("{T.Await()}")
