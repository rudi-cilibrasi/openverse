# (#513) a rush arm that becomes a task while its Sleep is due goes on at
# its turn in the scheduler's pass (no event: the same output as before
# awaiters ran inside Signal)
Main()<suspends>:void =
    rush:
        block:
            Sleep(0.01)
            Print("winner")
        block:
            Sleep(0.01)
            Print("loser")
    Print("after rush")
    Sleep(0.1)
    Print("done")
