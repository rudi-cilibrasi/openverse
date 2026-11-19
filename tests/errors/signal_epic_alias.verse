# expect: this call may signal an event (event.Signal) in a failure context
# (#515) through an alias of the event: UEFN 43.12 refuses it with error 3512
# (tests/conformance/versevm/signal-alias.verse)
Main():void =
    E := event(int){}
    Alias := E
    if (Alias.Signal(1), false?):
        Print("unexpected")
    Print("after")
