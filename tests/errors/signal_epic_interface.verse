# expect: this call may signal an event (event.Signal) in a failure context
# (#515) through a signalable(int) view of the event: UEFN 43.12 refuses it
# with error 3512, naming signalable's Signal
# (tests/conformance/versevm/signal-interface.verse)
Main():void =
    E := event(int){}
    View:signalable(int) = E
    if (View.Signal(1), false?):
        Print("unexpected")
    Print("after")
