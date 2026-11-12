Main()<suspends>:void=
    sync:
        block:
            Sleep(0.15)
            Print("timer")
        block:
            Print("peer")
            Sleep(0.0)
            Print("tick 1")
            Sleep(0.0)
            Print("tick 2")
            Sleep(0.0)
            Print("tick 3")
            Sleep(0.0)
            Print("tick 4")
            Sleep(0.0)
            Print("tick 5")
