Main():void =
    E := event(int){}
    if (E.Signal(1), false?):
        Print("OVPROBE unexpected")
    Print("OVPROBE after")
