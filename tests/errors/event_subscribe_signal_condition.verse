# expect: 18:16: this call may signal an event (event.Signal) in a failure context, which the no_rollback effect of an event's Signal does not allow (Epic's Verse compiler, UEFN 43.12: error 3512; #515)
# (#724) An event with a function subscribed, signalled in a failure
# context: refused at that Signal (its no_rollback effect, #515), and only
# there: the Subscribe is admitted. Epic's Verse compiler (UEFN 43.12,
# build ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM") refuses this
# program with error 3512 at the condition's Signal and nothing else
# (tests/conformance/versevm/signal-subscribe.verse, rewritten).
counter := class:
    var Seen:int = 0

    Receive(N:int)<transacts>:void =
        set Seen = N

Main():void =
    E := event(int){}
    C := counter{}
    Subscription := E.Subscribe(C.Receive)
    if (E.Signal(1), false?):
        Print("unexpected")
    Print("after failure {C.Seen}")
    E.Signal(2)
    Print("after success {C.Seen}")
    Subscription.Cancel()
