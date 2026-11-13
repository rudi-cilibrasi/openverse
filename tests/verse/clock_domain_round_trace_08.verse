Main()<suspends>:void=
    sync:
        block:
            Sleep(0.05000000000000001)
            Print("timer")
        block:
            Print("peer")
            Sleep(0.01)
            Print("tick 1")
            Sleep(0.01)
            Print("tick 2")
            Sleep(0.01)
            Print("tick 3")
