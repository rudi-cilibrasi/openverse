Wait(E:event(int))<transacts><suspends>:int =
    E.Await()

Main()<suspends>:void =
    E := event(int){}
    branch:
        N := Wait(E)
        Print("OVPROBE received {N}")
    Sleep(0.1)
    E.Signal(5)
    Sleep(0.1)
