# spawning and awaiting in a loop; tasks that are done are dropped (#156)
Job(N:int)<suspends>:int =
    Sleep(0.01)
    N
Main()<suspends>:void =
    var Sum:int = 0
    for (I := 1..300):
        T := spawn{Job(I)}
        set Sum += T.Await()
    Print("{Sum}")
