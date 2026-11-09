# Main spawns A; A's first run spawns B, whose first run awaits a cancelled
# task. Expected: B is cancelled (B defer), A goes on: B defer / A goes on /
# A end / A defer / main end
W()<suspends>:int =
    Sleep(9.0)
    1
B(T:task(int))<suspends>:int =
    defer:
        Print("B defer")
    T.Await()
A()<suspends>:int =
    defer:
        Print("A defer")
    T := spawn{W()}
    T.Cancel()
    spawn{B(T)}
    Print("A goes on")
    Sleep(0.2)
    Print("A end")
    0
Main()<suspends>:void =
    spawn{A()}
    Sleep(1.0)
    Print("main end")
