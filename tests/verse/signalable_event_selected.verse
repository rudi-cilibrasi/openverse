Main():void =
    E := event(int){}
    View:signalable(int) = E
    if (true?):
        View.Signal(1)
        Print("selected")
