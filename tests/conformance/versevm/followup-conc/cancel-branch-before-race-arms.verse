# As cancel-branch-before-sync-arms, with a race instead of the sync: a race
# arm cancelled (it loses) that started a child branch (in a helper that
# returned) and then waits in a race of two arms, each with a defer.
# Epic (UEFN 43.12, cancel-branch-before-sync-arms) cancels the arms of the
# sync a cancelled task waits in first, last started first, as its newest
# children, then its branch, then its own defers. OpenVerse (#724) treats a
# race's arms the same way.
# OpenVerse prints:
#   winner done | arm two cleanup | arm one cleanup | branch cleanup | loser cleanup | after race | after wait
# If a race (an outer task with an inner task per arm, the Book's
# AsyncContextCancellation.versetest) stopped its arms in the order they
# started, or after the branch:
#   winner done | arm one cleanup | arm two cleanup | branch cleanup | loser cleanup | after race | after wait
#   winner done | branch cleanup | arm two cleanup | arm one cleanup | loser cleanup | after race | after wait
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        Sleep(10.0)

Loser()<suspends>:void =
    defer:
        Print("OVPROBE loser cleanup")
    Helper()
    race:
        block:
            defer:
                Print("OVPROBE arm one cleanup")
            Sleep(10.0)
        block:
            defer:
                Print("OVPROBE arm two cleanup")
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
