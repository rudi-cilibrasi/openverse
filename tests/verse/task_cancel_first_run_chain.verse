# the same, in a task started by a task, which goes on to its end (#253)
W()<suspends>:int =
    Sleep(9.0)
    1
F()<suspends>:int =
    defer:
        Print("F defer")
    T := spawn{W()}
    T.Cancel()
    T.Await()
Spawner()<suspends>:int =
    defer:
        Print("Spawner defer")
    spawn{F()}
    Sleep(0.1)
    Print("spawner goes on")
    5
Main()<suspends>:void =
    S := spawn{Spawner()}
    Sleep(0.5)
    Print("main goes on")
