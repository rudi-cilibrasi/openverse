# deep chains of waiting frames (#362) cancelled, raced and synced: a task whose
# recursion of depth 8 waits at its leaf is cancelled (each level's defer runs,
# leaf first); a race between two deep chains (the loser's levels unwind); a
# sync of two; a leaf that spawns and awaits a task of its own, and starts a
# branch; a generic recursion
Down(N:int, Tag:string)<suspends>:int =
    defer:
        Print("{Tag} unwinds {N}")
    if (N = 0):
        Sleep(Inf)
        0
    else:
        Down(N - 1, Tag) + 1
Count(N:int, K:int)<suspends>:int =
    if (N = 0):
        for (I := 1..K):
            Sleep(0.01)
        K
    else:
        Count(N - 1, K) + 1
Child(X:int)<suspends>:int =
    Sleep(0.01)
    X * 10
Spawner(N:int)<suspends>:int =
    if (N = 0):
        T := spawn{Child(4)}
        branch:
            Sleep(0.01)
            Print("branch ran")
        V := T.Await()
        Sleep(0.01)
        V
    else:
        Spawner(N - 1) + 1
Gen(N:int, X:t where t:type)<suspends>:t =
    if (N = 0):
        Sleep(0.01)
        Sleep(0.01)
        X
    else:
        Gen(N - 1, X)
Main()<suspends>:void =
    T := spawn{Down(8, "a")}
    Sleep(0.01)
    Sleep(0.01)
    T.Cancel()
    Print("cancelled")
    W := race:
        Down(6, "loser")
        Count(5, 3)
    Print("race {W}")
    S := sync:
        Count(7, 2)
        Count(4, 5)
    Print("sync {S(0)} {S(1)}")
    Print("spawner {Spawner(6)}")
    Print("gen {Gen(9, "x")} {Gen(7, 3)}")
