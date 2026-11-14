CountTo(N:int)<suspends>:int =
    var I:int = 0
    defer: Print("counter stopped")
    loop:
        Sleep(0.01)
        set I += 1
        if (I = N) then return I

Main()<suspends>:void =
    T := spawn{CountTo(2)}
    Print("started")
    Print("{T.Await()}")
    race:
        block:
            CountTo(100)
            Print("wrong")
        Sleep(0.01)
    Print("cancelled")
