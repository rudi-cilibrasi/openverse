# (#513) --event-fifo: a rush arm that becomes a task while its Sleep is due
# goes on at its turn, as without the option (no event: the same output)
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
