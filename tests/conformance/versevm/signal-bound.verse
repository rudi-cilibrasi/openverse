Main():void =
    E := event(int){}
    Send := E.Signal
    if (Send(1), false?):
        Print("OVPROBE unexpected")
    Print("OVPROBE after")
