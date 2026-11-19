# expect: this call may signal an event (event.Signal (called as a function value)) in a failure context
# (#515) through the event's Signal bound as a function value: UEFN 43.12
# refuses the call with error 3512 (tests/conformance/versevm/signal-bound.verse)
Main():void =
    E := event(int){}
    Send := E.Signal
    if (Send(1), false?):
        Print("unexpected")
    Print("after")
