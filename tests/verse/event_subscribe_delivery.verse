# (#724) What an event's Signal does with the functions subscribed to it,
# as Epic's Verse VM does (UEFN 43.12, build
# ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM", 2026-11-19: the
# probes in tests/conformance/versevm/followup-event/ named here): a task
# awaiting the event goes on inside Signal before the functions are called
# (await-and-subscribe); the Signal then calls the functions subscribed at
# that point, so one that the resumed awaiter subscribes too
# (subscribe-from-awaiter), but not one that a called function subscribes
# (subscribe-during-signal), each skipped if cancelled before its turn
# (cancel-during-signal); a second Cancel does nothing (cancel-twice); a
# function subscribed twice is called twice (same-handler-twice); a Signal
# made by a subscribed function calls them at once, depth first
# (nested-signal-in-handler). The order of the functions is openverse's:
# the order they subscribed, where the Verse VM's varies from one Signal to
# the next (subscribe-order), so a program must not rely on it.
tally := class:
    Name:string
    Note(N:int):void = Print("{Name} {N}")
holder := class:
    E:event(int)
    var Victim:?cancelable = false
    var Added:?cancelable = false
    Late(N:int):void = Print("late {N}")
    On(N:int):void =
        Print("holder {N}")
        if (V := Victim?) then V.Cancel()
        if (not Added?) then set Added = option{E.Subscribe(Late)}
relay := class:
    E:event(int)
    OnRelay(N:int):void =
        Print("in {N}")
        if (N < 3) then E.Signal(N + 1)
        Print("out {N}")
Plain(N:int):void = Print("plain {N}")
Twice(N:int):void = Print("twice {N}")
FromWaiter(N:int):void = Print("from waiter {N}")
Waiter(E:event(int), Subscribe:logic)<suspends>:void =
    V := E.Await()
    Print("awaited {V}")
    if (Subscribe?) then S := E.Subscribe(FromWaiter)
Main()<suspends>:void =
    E := event(int){}
    A := tally{Name := "a"}
    B := tally{Name := "b"}
    SA := E.Subscribe(A.Note)
    SB := E.Subscribe(B.Note)
    SP := E.Subscribe(Plain)
    E.Signal(1)
    SB.Cancel()
    SB.Cancel()
    E.Signal(2)
    H := holder{E := E}
    SH := E.Subscribe(H.On)
    set H.Victim = option{SP}
    E.Signal(3)
    E.Signal(4)
    SA.Cancel()
    SH.Cancel()
    if (L := H.Added?) then L.Cancel()
    S1 := E.Subscribe(Twice)
    S2 := E.Subscribe(Twice)
    E.Signal(5)
    S1.Cancel()
    E.Signal(6)
    S2.Cancel()
    F := event(int){}
    R := relay{E := F}
    SR := F.Subscribe(R.OnRelay)
    F.Signal(1)
    SR.Cancel()
    G := event(int){}
    SG := G.Subscribe(Plain)
    spawn{Waiter(G, true)}
    G.Signal(7)
    Print("after 7")
    G.Signal(8)
    Print("done")
