# Main's sync: arm 1 awaits a cancelled task, arm 2 spawns C before waiting.
# Expected: Main awaited a cancelled task, so Main is cancelled at its wait
# and the program ends: "Main defer" only (C's defer does not run: the
# program ends with Main).
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
