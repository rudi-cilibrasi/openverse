Main():void =
    E := event(int){}
    View:signalable(int) = E
    View.Signal(1)
    Print("OVPROBE after")
