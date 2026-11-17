Main():void =
    E := event(int){}
    View:signalable(int) = E
    if (View.Signal(1), false?):
        Print("OVPROBE unexpected")
    Print("OVPROBE after")
