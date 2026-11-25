# followup-corners (#724): A spawned task with a child branch (whose defer
# prints) awaits an event, and a second task awaits the same event behind
# it. Signal resumes the first, which ends at once: is its branch's defer
# run before the second awaiter is resumed?
# OpenVerse (Lean and C agreeing): ran, runner resumed | branch cleanup |
# second awaiter | after signal | after wait (the task's children are
# stopped when its code ends, inside Signal, before the next awaiter runs).
# If Epic prints the same, OpenVerse agrees. If it prints runner resumed |
# second awaiter | branch cleanup | ..., or branch cleanup after after
# signal, a task's children are cancelled after the Signal's other awaiters
# have run (or at a later update): OpenVerse would defer that cancellation.
# Not yet compiled or run by UEFN.
Runner(E:event())<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        Sleep(10.0)
    E.Await()
    Print("OVPROBE runner resumed")

Second(E:event())<suspends>:void =
    E.Await()
    Print("OVPROBE second awaiter")

Main()<suspends>:void =
    E := event(){}
    spawn{Runner(E)}
    spawn{Second(E)}
    Sleep(0.1)
    E.Signal()
    Print("OVPROBE after signal")
    Sleep(0.1)
    Print("OVPROBE after wait")
