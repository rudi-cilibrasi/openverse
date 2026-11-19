# A sync arm cancelled because the task that runs the sync is (a race arm
# that loses), the sync arm having a child branch (started in a helper that
# returned): is the sync arm's child stopped before the sync arm's own
# defer, as a cancelled race arm's is (branch-cancel-order, UEFN 43.12)?
# OpenVerse (#724) cancels every task the same way, children first.
# OpenVerse prints:
#   winner done | branch cleanup | sync arm cleanup | loser cleanup | after race | after wait
# If a sync arm cancelled with its task unwound before its children:
#   winner done | sync arm cleanup | branch cleanup | loser cleanup | after race | after wait
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        Sleep(10.0)

Loser()<suspends>:void =
    defer:
        Print("OVPROBE loser cleanup")
    sync:
        block:
            defer:
                Print("OVPROBE sync arm cleanup")
            Helper()
            Sleep(10.0)
        block:
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
