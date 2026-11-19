# A race arm cancelled (it loses) with two child branches, each started in a
# helper that returned: which child is stopped first?
# Epic (UEFN 43.12, branch-cancel-order) stops a cancelled task's child
# before the task's own defers run; with one child only. OpenVerse (#724)
# stops a task's children newest first, at its end and at its cancel.
# OpenVerse prints:
#   winner done | second cleanup | first cleanup | arm cleanup | after race | after wait
# If the oldest were stopped first:
#   winner done | first cleanup | second cleanup | arm cleanup | after race | after wait
First()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE first cleanup")
        Sleep(10.0)

Second()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE second cleanup")
        Sleep(10.0)

Loser()<suspends>:void =
    defer:
        Print("OVPROBE arm cleanup")
    First()
    Second()
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
