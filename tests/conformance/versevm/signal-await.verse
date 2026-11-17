Main()<suspends>:void =
    E := event(int){}
    branch:
        Print("OVPROBE waiting")
        N := E.Await()
        Print("OVPROBE received {N}")
    Sleep(0.1)
    if (E.Signal(1), false?):
        Print("OVPROBE unexpected")
    E.Signal(2)
    Sleep(0.1)
