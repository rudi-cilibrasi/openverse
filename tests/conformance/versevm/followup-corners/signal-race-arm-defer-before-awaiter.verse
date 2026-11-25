# followup-corners (#724): The same with the first awaiter a race arm that
# owns the branch: the arm is resumed by Signal and wins the race at once.
# Are its branch's defer, the losing arm's defer and the code after the race
# run before the second awaiter of the event is resumed?
# OpenVerse (Lean and C agreeing): ran, arm resumed | branch cleanup | loser
# cleanup | after race | second awaiter | after signal | after wait (the
# arm's task ends, its children and the loser are cancelled and the race's
# code goes on, all inside Signal before the next awaiter).
# If Epic prints the same, OpenVerse agrees. If second awaiter comes before
# branch cleanup, loser cleanup or after race, the event's other awaiters
# run before a finished race arm is cleaned up or before the race's task
# goes on: OpenVerse would order them so.
# Not yet compiled or run by UEFN.
Runner(E:event())<suspends>:void =
    race:
        block:
            branch:
                defer:
                    Print("OVPROBE branch cleanup")
                Sleep(10.0)
            E.Await()
            Print("OVPROBE arm resumed")
        block:
            defer:
                Print("OVPROBE loser cleanup")
            Sleep(10.0)
    Print("OVPROBE after race")

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
