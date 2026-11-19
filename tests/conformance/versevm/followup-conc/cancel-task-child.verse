# A spawned task cancelled by Cancel(), with a child branch (started in a
# helper that returned): is its child stopped before its own defer, as a
# race arm's is when it loses (branch-cancel-order, UEFN 43.12)?
# OpenVerse (#724) cancels every task the same way, children first, and
# unwinds a task inside its Cancel().
# OpenVerse prints:
#   branch cleanup | runner cleanup | cancelled | after wait
# If the task's own defers ran first:
#   runner cleanup | branch cleanup | cancelled | after wait
# (and `cancelled` first if Cancel() only asks, the task unwinding later)
Helper()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        Sleep(10.0)

Runner()<suspends>:void =
    defer:
        Print("OVPROBE runner cleanup")
    Helper()
    Sleep(10.0)

Main()<suspends>:void =
    T := spawn{Runner()}
    Sleep(0.1)
    T.Cancel()
    Print("OVPROBE cancelled")
    Sleep(0.1)
    Print("OVPROBE after wait")
