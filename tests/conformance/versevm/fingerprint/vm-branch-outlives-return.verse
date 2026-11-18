# The Book (docs/14_concurrency.md, "The branch Expression", example 13)
# cancels a branch when the function that ran it returns: its defer runs and
# its last line does not. Reported for Epic's new Verse VM: a branch runs
# until its parent task ends, so the last line runs too.
FireAndForget()<suspends>:void =
    branch:
        defer:
            Print("OVPROBE branch cleanup")
        Sleep(0.05)
        Print("OVPROBE branch body finished")
    Print("OVPROBE function returning")

Main()<suspends>:void =
    FireAndForget()
    Print("OVPROBE returned")
    Sleep(0.2)
    Print("OVPROBE after wait")
