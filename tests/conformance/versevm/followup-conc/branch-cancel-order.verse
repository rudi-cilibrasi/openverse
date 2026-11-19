# A race arm cancelled (it loses) while its code waits and a branch it
# started in a helper that returned still runs: in which order do the arm's
# own defer and its child branch's defer run? (A race arm is a task of its
# own, the branch its child: the Book's AsyncContextCancellation.versetest.)
# OpenVerse (#724) prints (the cancelled task's code unwinds, then its
# children are stopped, as when a task ends):
#   winner done | arm cleanup | branch cleanup | after race | after wait
# If children were stopped first:
#   winner done | branch cleanup | arm cleanup | after race | after wait
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        Sleep(10.0)

Loser()<suspends>:void =
    defer:
        Print("OVPROBE arm cleanup")
    Helper()
    Sleep(10.0)

Main()<suspends>:void =
    race:
        Loser()
        block:
            Sleep(0.1)
            Print("OVPROBE winner done")
    Print("OVPROBE after race")
    Sleep(0.1)
    Print("OVPROBE after wait")
