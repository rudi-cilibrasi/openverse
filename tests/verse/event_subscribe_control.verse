# (#724) An event's Subscribe with a <transacts> method, signalled outside
# every failure context, then cancelled. Epic's Verse VM (UEFN 43.12, build
# ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM") admits this program
# and prints "after success 2" (tests/conformance/versevm/signal-subscribe-control.verse,
# rewritten).
counter := class:
    var Seen:int = 0

    Receive(N:int)<transacts>:void =
        set Seen = N

Main():void =
    E := event(int){}
    C := counter{}
    Subscription := E.Subscribe(C.Receive)
    E.Signal(2)
    Print("after success {C.Seen}")
    Subscription.Cancel()
