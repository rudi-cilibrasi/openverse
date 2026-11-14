# Main's sync: arm 1 awaits a cancelled task, arm 2 spawns C before waiting.
# Expected: arm 1 waits for ever (the Book's API, task, Await), so the sync
# never ends; arm 2 and C go on to their ends, and then no task can run:
# the program ends as a Main that waits with no task able to run does
# (exit 2), Main's defer not run: arm 2 goes on / C end / C defer.
W()<suspends>:int =
    Sleep(9.0)
    1
C()<suspends>:int =
    defer:
        Print("C defer")
    Sleep(0.5)
    Print("C end")
    0
Main()<suspends>:void =
    defer:
        Print("Main defer")
    T := spawn{W()}
    T.Cancel()
    sync:
        T.Await()
        block:
            spawn{C()}
            Sleep(0.2)
            Print("arm 2 goes on")
            2
    Print("never")
