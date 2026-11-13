# deep chains of waiting frames inside the arms of sync, race and rush (#362):
# each arm records the waiting frame its chain found and is resumed from it
# while it waits; a race against a timeout, a sync of two deep arms, a race
# nested in a sync arm, a rush whose deep loser goes on, and a task cancelled
# while deep in an arm (its levels unwind, leaf first)
Deep(N:int, K:int, Tag:string)<suspends>:int =
    defer:
        if (N = 0 or N = 7):
            Print("{Tag} {N} unwinds")
    if (N = 0):
        for (I := 1..K):
            Sleep(0.01)
        K
    else:
        Deep(N - 1, K, Tag) + 1
Worker()<suspends>:int =
    sync:
        Deep(12, 1000, "w1")
        Deep(9, 1000, "w2")
    0
Main()<suspends>:void =
    R := race:
        Deep(20, 30, "fast")
        block:
            Sleep(100.0)
            -1
    Print("race {R}")
    S := sync:
        Deep(15, 20, "a")
        Deep(10, 40, "b")
    Print("sync {S(0)} {S(1)}")
    T := sync:
        race:
            Deep(8, 50, "slow")
            Deep(11, 10, "quick")
        Deep(6, 25, "side")
    Print("nested {T(0)} {T(1)}")
    U := rush:
        Deep(9, 60, "loser")
        Deep(5, 5, "winner")
    Print("rush {U}")
    W := spawn{Worker()}
    for (I := 1..20):
        Sleep(0.01)
    W.Cancel()
    Print("done")
