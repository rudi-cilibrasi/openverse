# return in an arm of race or sync returns from the function: the other arms are cancelled, the defers run, also from a nested sync (#156)
Slow(Tag:string)<suspends>:void =
    defer:
        Print("{Tag} unwound")
    Sleep(5.0)
Find(N:int)<suspends>:string =
    defer:
        Print("Find {N} defer")
    race:
        block:
            Sleep(1.0)
            if (N > 0):
                return "found {N}"
            Sleep(1.0)
        Slow("race loser")
    "not found"
Both(N:int)<suspends>:int =
    defer:
        Print("Both defer")
    R := sync:
        block:
            defer:
                Print("arm a defer")
            Sleep(0.5)
            if (N = 1) then return 100
            1
        block:
            Slow("sync sibling")
            2
    R(0) + R(1)
Deep()<suspends>:int =
    sync:
        sync:
            block:
                Sleep(0.2)
                return 7
            Slow("inner sibling")
        Slow("outer sibling")
    0
Main()<suspends>:void =
    Print(Find(1))
    Print(Find(0))
    Print("{Both(1)}")
    Print("{Deep()}")
