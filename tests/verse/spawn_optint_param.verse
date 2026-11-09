# a suspends function with a ?int parameter that awaits a task: the task
# temporary's Root starts as false, not as the parameter (#249)
Id(N:int)<suspends>:int =
    Sleep(0.1)
    N
F0(X:?int)<suspends>:int =
    T := spawn{Id(1)}
    T.Await()
Main()<suspends>:void =
    Print("result {F0(false)}")
