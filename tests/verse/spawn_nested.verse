# a spawn in a spawned call's arguments starts first (#180)
Run(N:int)<suspends>:int =
    Sleep(1.0)
    Print("run {N}")
    N
Take(T:task(int), K:int)<suspends>:int =
    Print("take {K}")
    T.Await() + K
agent := class:
    Go()<suspends>:int =
        Sleep(0.5)
        1
fast := class(agent):
    Go<override>()<suspends>:int = 2
Kick(A:agent):task(int) = spawn{Take(spawn{A.Go()}, 100)}
holder := class:
    T:task(int) = spawn{Take(spawn{Run(7)}, 70)}
Main()<suspends>:void =
    T := spawn{Take(spawn{Run(1)}, 10)}
    U := spawn{Take(spawn{Take(spawn{Run(2)}, 20)}, 200)}
    A:agent = fast{}
    V := Kick(A)
    H := holder{}
    Print("{T.Await()} {U.Await()} {V.Await()} {H.T.Await()}")
