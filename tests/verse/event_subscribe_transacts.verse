# (#724) An event's Subscribe: Epic's event(t) has it (subscribable_event is
# an openverse extension). It is admitted in a <transacts> function and
# gives a cancelable; a later Signal calls the subscribed method before the
# next statement; Cancel is valid. Epic's Verse VM (UEFN 43.12, build
# ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM") admits this program
# and prints "seen 4" (tests/conformance/versevm/followup/subscribe-in-transacts.verse).
counter := class:
    var Seen:int = 0

    Receive(N:int):void =
        set Seen = N

Attach(E:event(int), C:counter)<transacts>:cancelable =
    E.Subscribe(C.Receive)

Main():void =
    E := event(int){}
    C := counter{}
    Subscription := Attach(E, C)
    E.Signal(4)
    Print("seen {C.Seen}")
    Subscription.Cancel()
