# Reference-clock trace: negative/NaN do not yield; zero always yields.
Main()<suspends>:void=
    sync:
        block:
            Print("immediate")
            Sleep(-1.0)
            Print("negative")
            Sleep(0.0/0.0)
            Print("nan")
            Sleep(0.0)
            Print("zero resumed")
        block:
            Print("peer started")
            Sleep(0.0)
            Print("peer resumed")
    sync:
        block:
            Sleep(0.04)
            Print("fraction resumed")
        block:
            Sleep(0.0)
            Print("tick one")
            Sleep(0.0)
            Print("tick two")
