Main()<suspends>:void=
    sync:
        block:
            Sleep(0.049999999999999996)
            Print("timer")
        block:
            Print("peer")
            Sleep(0.01)
            Print("tick 1")
            Sleep(0.01)
            Print("tick 2")
