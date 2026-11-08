# spawn starts a task at once, up to its first wait, and gives a task(t); Await waits for its result (#156)
Worker(Name:string, N:int)<suspends>:int =
    var I:int = 0
    loop:
        if (I >= N) then break
        Sleep(1.0)
        set I += 1
        Print("{Name} {I}")
    N * 100
Main()<suspends>:void =
    T1 := spawn{Worker("a", 3)}
    T2 := spawn{Worker("b", 2)}
    Print("spawned")
    Sleep(1.5)
    Print("main awake")
    R2 := T2.Await()
    Print("b gave {R2}")
    R1 := T1.Await()
    Print("a gave {R1}")
    R3 := T1.Await()
    Print("again {R3}")
