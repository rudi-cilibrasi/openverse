# Main ends inside a Signal (or a task's end) that resumed it: its children
# are stopped there, as a task's are when it ends, before the awaiters after
# it in that Signal go on (#723, scripts/fuzz-model-sched.sh seeds 20776326
# and 20777477); then the signalling task goes on to its next wait, and the
# program ends.
Waiter(E:event())<suspends>:void =
    Sleep(0.1)
    E.Await()
    Print("waiter woke")
Signaller(E:event())<suspends>:void =
    Sleep(0.2)
    E.Signal()
    Print("signalled")
    Sleep(0.1)
    Print("not reached")
Main()<suspends>:void =
    E := event(){}
    spawn{Signaller(E)}
    spawn{Waiter(E)}
    branch:
        defer:
            Print("older branch defer")
        Sleep(1.0)
    branch:
        defer:
            Print("newer branch defer")
        branch:
            defer:
                Print("branch's branch defer")
            Sleep(1.0)
        Sleep(1.0)
    E.Await()
    Print("main end")
