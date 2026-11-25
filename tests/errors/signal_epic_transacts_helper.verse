# expect: 6:12: this call may signal an event (event.Signal), whose Signal has the no_rollback effect, in Send, whose effects (<transacts>) exclude no_rollback (Epic's Verse compiler, UEFN 43.12: error 3512; #515)
# (#515) a <transacts> function cannot signal an event, even one called
# outside every failure context: UEFN 43.12 refuses the Signal in Send with
# error 3512 (tests/conformance/versevm/signal-generic-control.verse)
Send(E:event(t), Value:t where t:type)<transacts>:void =
    E.Signal(Value)
Main():void =
    E := event(int){}
    Send(E, 1)
    Print("after")
