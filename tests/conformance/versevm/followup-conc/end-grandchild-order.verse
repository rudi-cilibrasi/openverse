# A spawned task that ends with a child branch (started in a helper that
# returned) that has started a branch of its own: the task's own defer runs
# first (branch-in-branch, UEFN 43.12), then its child is stopped; is the
# child stopped as a cancelled task is (branch-cancel-order: its own child
# first), or does it run its own defers first?
# OpenVerse (#724): a stopped child is cancelled, its children first.
# OpenVerse prints:
#   runner ending | runner cleanup | grandchild cleanup | child cleanup | after wait
# If the child ran its own defers first:
#   runner ending | runner cleanup | child cleanup | grandchild cleanup | after wait
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE child cleanup")
        branch:
            defer:
                Print("OVPROBE grandchild cleanup")
            Sleep(10.0)
        Sleep(10.0)

Runner()<suspends>:void =
    defer:
        Print("OVPROBE runner cleanup")
    Helper()
    Sleep(0.1)
    Print("OVPROBE runner ending")

Main()<suspends>:void =
    spawn{Runner()}
    Sleep(0.3)
    Print("OVPROBE after wait")
