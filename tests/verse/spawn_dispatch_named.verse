# spawned dispatches whose implementations take named arguments with their
# own defaults, in immediate code, field defaults and methods (#173)
agent := class:
    Name:string
    Run(?N:int = 1)<suspends>:int =
        Print("agent {Name} run {N}")
        N
    Kick():task(int) = spawn{Run(?N := 7)}
fast := class(agent):
    Run<override>(?N:int = 2)<suspends>:int =
        Sleep(1.0)
        Print("fast {Name} run {N}")
        N * 2
Make(I:int):agent =
    Print("make {I}")
    if (I = 0) then agent{Name := "a"} else fast{Name := "f"}
Global():agent = fast{Name := "g"}
holder := class:
    T:task(int) = spawn{Global().Run()}
Main()<suspends>:void =
    T1 := spawn{Make(1).Run(?N := 3)}
    T2 := spawn{Make(0).Run()}
    T3 := Make(1).Kick()
    H := holder{}
    Print("{T1.Await()} {T2.Await()} {T3.Await()} {H.T.Await()}")
