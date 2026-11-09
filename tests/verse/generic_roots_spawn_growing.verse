# a spawn in a generic function that calls itself at ever bigger types: the
# spawned task is a root of the scheduler at its type arguments (#244)
Depth(X:t, N:int where t:type)<suspends>:int =
    if (N > 0):
        T := spawn{Depth(array{X}, N - 1)}
        T.Await() + 1
    else:
        Sleep(0.1)
        0
Main()<suspends>:void = Print("{Depth(1, 3)}")
