# A race arm cancelled (it loses) that started a branch (in a helper that
# returned), then waits in a sync whose first arm started a branch of its
# own (in another helper) and waits too: the first branch is the race arm's
# child, the second the sync arm's (a sync arm is a task, the Book's
# AsyncContextCancellation.versetest; branch-in-sync-arm, UEFN 43.12).
# Epic (UEFN 43.12, cancel-branch-before-sync-arms) cancels the sync's arms
# first, last started first, then the cancelled task's branch, then its own
# defers; each arm stops its own children before its defers
# (cancel-sync-arm-child).
# OpenVerse (#724) prints:
#   winner done | arm two cleanup | arm branch cleanup | arm one cleanup | task branch cleanup | loser cleanup | after race | after wait
# If the branch started in the sync arm belonged to the race arm (the task
# that runs the sync), stopped newest first after the sync's arms:
#   winner done | arm two cleanup | arm one cleanup | arm branch cleanup | task branch cleanup | loser cleanup | after race | after wait
First()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE task branch cleanup")
        Sleep(10.0)

Second()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE arm branch cleanup")
        Sleep(10.0)

Loser()<suspends>:void =
    defer:
        Print("OVPROBE loser cleanup")
    First()
    sync:
        block:
            defer:
                Print("OVPROBE arm one cleanup")
            Second()
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
