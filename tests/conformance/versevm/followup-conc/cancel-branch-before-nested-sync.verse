# As cancel-branch-before-sync-arms, with the sync one call deeper, in a
# function with a defer of its own: a race arm cancelled (it loses) that
# started a child branch (in a helper that returned), then called Inner,
# which waits in a sync of two arms. Is the branch stopped before Inner's
# defer (all of a cancelled task's children before any of its defers, its
# newest, the sync's arms, first), or once the frame that holds the arms
# has unwound?
# OpenVerse (#724) prints:
#   winner done | arm two cleanup | arm one cleanup | branch cleanup | inner cleanup | loser cleanup | after race | after wait
# If the frame holding the arms unwound before the branch was stopped:
#   winner done | arm two cleanup | arm one cleanup | inner cleanup | branch cleanup | loser cleanup | after race | after wait
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) printed
#   winner done | arm two cleanup | arm one cleanup | branch cleanup | inner cleanup | loser cleanup | after race | after wait
# as OpenVerse does.
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        Sleep(10.0)

Inner()<suspends>:void =
    defer:
        Print("OVPROBE inner cleanup")
    sync:
        block:
            defer:
                Print("OVPROBE arm one cleanup")
            Sleep(10.0)
        block:
            defer:
                Print("OVPROBE arm two cleanup")
            Sleep(10.0)

Loser()<suspends>:void =
    defer:
        Print("OVPROBE loser cleanup")
    Helper()
    Inner()

Main()<suspends>:void =
    race:
        Loser()
        block:
            Sleep(0.1)
            Print("OVPROBE winner done")
    Print("OVPROBE after race")
    Sleep(0.1)
    Print("OVPROBE after wait")
