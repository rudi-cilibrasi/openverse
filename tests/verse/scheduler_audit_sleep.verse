# Reference-clock trace: negative, NaN and zero durations complete at once,
# without yielding (zero: the Book's tested examples in ch. 14); a positive
# one waits for the first tick at or after its deadline, at least one.
Main()<suspends>:void=
    sync:
        block:
            Print("immediate")
            Sleep(-1.0)
            Print("negative")
            Sleep(0.0/0.0)
            Print("nan")
            Sleep(0.0)
            Print("zero, at once")
        block:
            Print("peer started")
            Sleep(0.01)
            Print("peer resumed")
    sync:
        block:
            Sleep(0.04)
            Print("fraction resumed")
        block:
            Sleep(0.01)
            Print("tick one")
            Sleep(0.01)
            Print("tick two")
