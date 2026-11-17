Main():void =
    E := event(int){}
    Send := E.Signal
    Send(1)
    Print("OVPROBE after")
