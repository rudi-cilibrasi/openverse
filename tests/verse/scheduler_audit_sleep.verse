# Reference-clock trace: negative and NaN durations complete at once,
# without yielding; zero yields and resumes on the next tick, as Epic's
# Verse VM and Blueprint VM do (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# probe vm-sleep-zero-yields); a positive one waits for the first tick at or
# after its deadline, at least one.
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
