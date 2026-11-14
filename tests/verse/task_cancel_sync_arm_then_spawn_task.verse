# The same in a spawned task's first run: F's sync arm 1 awaits a cancelled
# task, arm 2 spawns C. Expected: F's sync never ends, and F waits for
# ever; arm 2 and C go on: arm 2 goes on / C end / C defer / main end
W()<suspends>:int =
    Sleep(9.0)
    1
C()<suspends>:int =
    defer:
        Print("C defer")
    Sleep(0.5)
    Print("C end")
    0
F(T:task(int))<suspends>:int =
    defer:
        Print("F defer")
    sync:
        T.Await()
        block:
            spawn{C()}
            Sleep(0.2)
            Print("arm 2 goes on")
            2
    Print("never")
    3
Main()<suspends>:void =
    T := spawn{W()}
    T.Cancel()
    spawn{F(T)}
    Sleep(1.0)
    Print("main end")
