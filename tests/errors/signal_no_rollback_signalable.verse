# expect: this call may signal an event
Main():void =
    E := event(int){}
    View:signalable(int) = E
    if (View.Signal(1), false?):
        Print("unexpected")
