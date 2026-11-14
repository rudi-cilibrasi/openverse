# Defers of a cancelled task, inside calls and blocks: innermost first.
# (Until the Book's rule that a cancelled task never resumes its awaiters,
# F was cancelled by awaiting a cancelled task; now Main cancels it.)
# Expected: H inner / H defer / G defer / F defer / main goes on / Main defer
H()<suspends>:int =
    defer:
        Print("H defer")
    block:
        defer:
            Print("H inner")
        Sleep(9.0)
        1
G()<suspends>:int =
    defer:
        Print("G defer")
    H() + 1
F()<suspends>:int =
    defer:
        Print("F defer")
    G()
Main()<suspends>:void =
    defer:
        Print("Main defer")
    T := spawn{F()}
    Sleep(0.1)
    T.Cancel()
    Print("main goes on")
