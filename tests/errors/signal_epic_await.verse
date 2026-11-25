# expect: 11:16: this call may signal an event (event.Signal) in a failure context
# (#515) with a task waiting on the event: UEFN 43.12 refuses the signal in
# the condition with error 3512, so no run can tell what the waiter receives
# (tests/conformance/versevm/signal-await.verse)
Main()<suspends>:void =
    E := event(int){}
    branch:
        N := E.Await()
        Print("received {N}")
    Sleep(0.1)
    if (E.Signal(1), false?):
        Print("unexpected")
    E.Signal(2)
    Sleep(0.1)
