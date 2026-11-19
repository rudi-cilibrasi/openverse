# expect: 6:12: this call may signal an event (event.Signal), whose Signal has the no_rollback effect, in Send
# (#515) the same helper called in a failure context: UEFN 43.12 reports the
# Signal in Send (error 3512), not the call of Send, which has no no_rollback
# (tests/conformance/versevm/signal-generic.verse)
Send(E:event(t), Value:t where t:type)<transacts>:void =
    E.Signal(Value)
Main():void =
    E := event(int){}
    if (Send(E, 1), false?):
        Print("unexpected")
    Print("after")
