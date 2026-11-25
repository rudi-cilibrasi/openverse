# A race arm cancelled (it loses) while its code waits and a branch it
# started in a helper that returned still runs: in which order do the arm's
# own defer and its child branch's defer run? (A race arm is a task of its
# own, the branch its child: the Book's AsyncContextCancellation.versetest.)
# OpenVerse (#724) printed, until Epic's result below (the cancelled task's
# code unwinds, then its children are stopped, as when a task ends):
#   winner done | arm cleanup | branch cleanup | after race | after wait
# If children were stopped first:
#   winner done | branch cleanup | arm cleanup | after race | after wait
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) printed
#   winner done | branch cleanup | arm cleanup | after race | after wait
# the second reading: a cancelled task's children are stopped before its own
# defers run. OpenVerse now prints it too (#724; the open cases of the rule
# are the cancel-*.verse and end-*.verse probes).
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
