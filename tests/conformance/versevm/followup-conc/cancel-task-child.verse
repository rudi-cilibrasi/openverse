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
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) refuses it at compile time, 3593: "Invalid
# access of epic_internal function `(/Verse.org/Concurrency/task:)Cancel`
# from control scope": user code cannot cancel a task on 43.12, so the
# question cannot be asked this way; a task's cancellation is asked through
# a race arm that loses (branch-cancel-order and the other cancel-*
# probes). OpenVerse admits T.Cancel() (its tests use it) and prints the
# lines above.
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
