# A cancelled call through a function value of a function with named
# parameters (#503): its default ran at the call, and its defer runs on
# cancellation.
log := class:
    var N:int = 0
    Next(What:string)<transacts>:int =
        set N += 1
        Print(What)
        N
Worker(L:log, ?Ticks:int = L.Next("default"))<suspends>:void =
    defer:
        Print("cleanup {Ticks}")
    Sleep(1.0)
    Print("done")
Main()<suspends>:void =
    L := log{}
    F:type{_(:log)<suspends>:void} = Worker
    race:
        F(L)
        Sleep(0.01)
    Print("after {L.N}")
