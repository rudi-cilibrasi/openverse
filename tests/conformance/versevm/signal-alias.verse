Main():void =
    E := event(int){}
    Alias := E
    if (Alias.Signal(1), false?):
        Print("OVPROBE unexpected")
    Print("OVPROBE after")
