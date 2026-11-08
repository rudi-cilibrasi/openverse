# spawn in immediate functions: the task starts on the scheduler at once and goes on under a suspends Main (#156)
Tick(Name:string, N:int)<suspends>:int =
    var I:int = 0
    loop:
        if (I >= N) then break
        Sleep(1.0)
        set I += 1
        Print("{Name} {I}")
    N
StartAll():[]task(int) =
    array{spawn{Tick("a", 2)}, spawn{Tick("b", 3)}}
MakeOne(N:int):task(int) = spawn{Tick("c", N)}
Main()<suspends>:void =
    Ts := StartAll()
    C := MakeOne(1)
    var Sum:int = 0
    for (T : Ts):
        set Sum += T.Await()
    Print("sum {Sum} c {C.Await()}")
