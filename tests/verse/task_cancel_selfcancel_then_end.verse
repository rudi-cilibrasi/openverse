# pre-existing (base too): a task cancels itself and then ends without a
# wait; it is "cancelled" after it ended: its defers run twice, and its
# result is lost (Main's Await is cancelled). Expected: defers once, and
# either "got 7" (no wait came) or a cancelled task, not both halves.
SelfEnd(Me:event(task(int)))<suspends>:int =
    defer:
        Print("selfend defer")
    T := Me.Await()
    T.Cancel()
    Print("ends without waiting")
    7
Main()<suspends>:void =
    defer:
        Print("Main defer")
    Me := event(task(int)){}
    S := spawn{SelfEnd(Me)}
    Me.Signal(S)
    Sleep(0.5)
    Print("got {S.Await()}")
