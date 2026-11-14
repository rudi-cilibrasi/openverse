# A's first run: a sync whose arm 1 awaits a cancelled task, whose arm 2
# spawns two siblings, the second of which spawns a grandchild. Arm 1 waits
# for ever, so A's sync never ends; none of the four is cancelled.
# Expected: B end x / B defer x / B end y / B defer y / G end / arm 2 ends /
# main end
W()<suspends>:int =
    Sleep(9.0)
    1
G()<suspends>:int =
    Sleep(0.2)
    Print("G end")
    0
B(N:string, Sub:logic)<suspends>:int =
    defer:
        Print("B defer {N}")
    if (Sub?) then spawn{G()}
    Sleep(0.1)
    Print("B end {N}")
    0
A()<suspends>:int =
    defer:
        Print("A defer")
    T := spawn{W()}
    T.Cancel()
    sync:
        T.Await()
        block:
            spawn{B("x", false)}
            spawn{B("y", true)}
            Sleep(0.5)
            Print("arm 2 ends")
            0
    Print("never")
    0
Main()<suspends>:void =
    spawn{A()}
    Sleep(1.0)
    Print("main end")
