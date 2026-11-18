# A branch that waits for an event, started by a function that then returns.
# With the Book's cancellation the waiter is gone before the signal; if the
# branch outlives the function (reported for the new Verse VM) it receives it.
Listen(E:event(int))<suspends>:void =
    branch:
        N := E.Await()
        Print("OVPROBE branch received {N}")
    Print("OVPROBE function returning")

Main()<suspends>:void =
    E := event(int){}
    Listen(E)
    Print("OVPROBE returned")
    E.Signal(7)
    Print("OVPROBE signaled")
    Sleep(0.1)
    Print("OVPROBE after wait")
