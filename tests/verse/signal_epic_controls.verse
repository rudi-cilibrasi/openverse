# (#515) what the no_rollback effect of an event's Signal still admits, as
# Epic's Verse compiler, UEFN 43.12 (build
# ++Fortnite+Release-43.12-CL-60598086), admits it: a Signal in an if's
# selected branch (tests/conformance/versevm/signal-control.verse), through
# a signalable(int) view outside a failure context (signal-interface-control),
# and in a function without specifiers, which has no_rollback, called outside
# every failure context
Relay(E:event(int), N:int):void =
    E.Signal(N)
Main()<suspends>:void =
    E := event(int){}
    branch:
        loop:
            N := E.Await()
            Print("received {N}")
    Sleep(0.0)
    if (true?):
        E.Signal(1)
        Print("selected")
    View:signalable(int) = E
    View.Signal(2)
    Relay(E, 3)
    Print("after")
