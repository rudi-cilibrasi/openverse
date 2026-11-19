# expect: 8:16: this call may signal an event (event.Signal) in a failure context, which the no_rollback effect of an event's Signal does not allow (Epic's Verse compiler, UEFN 43.12: error 3512; #515)
# (#515) the default: an event's Signal has the no_rollback effect, which a
# failure context does not allow. Epic's Verse compiler, UEFN 43.12 (build
# ++Fortnite+Release-43.12-CL-60598086), refuses this body with error 3512
# (tests/conformance/versevm/signal-direct.verse)
Main():void =
    E := event(int){}
    if (E.Signal(1), false?):
        Print("unexpected")
    Print("after")
