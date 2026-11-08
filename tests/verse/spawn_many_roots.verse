# many roots alive at once, each started by the last (#215): adding a root
# must not copy the heap, or the reference interpreter takes quadratic time
Chain(N:int, Left:int)<suspends>:int =
    if (Left > 0):
        T := spawn{Chain(N + 1, Left - 1)}
    Sleep(1.0)
    N
Main()<suspends>:void =
    T := spawn{Chain(0, 8000)}
    Sleep(2.0)
    Print("{T.Await()}")
