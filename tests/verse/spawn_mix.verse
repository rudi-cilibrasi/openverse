# tasks that finish at once, several tasks and waiters, generic tasks, spawn in an arm, and the program ending with tasks running (#156)
Quick(N:int)<suspends>:int = N + 1
Slow(Name:string, D:float)<suspends>:string =
    Sleep(D)
    Print("{Name} done")
    Name
Echo(X:t where t:type)<suspends>:t =
    Sleep(0.5)
    X
Watcher(T:task(string))<suspends>:void =
    Print("watcher got {T.Await()}")
Forever()<suspends>:void =
    loop:
        Sleep(1.0)
        Print("tick")
Main()<suspends>:void =
    Q := spawn{Quick(41)}
    Print("quick {Q.Await()}")
    var Ts:[]task(string) = array{}
    for (I := 1..3):
        set Ts += array{spawn{Slow("w{I}", 3.0 - I * 0.5)}}
    if (T0 := Ts[0]):
        W := spawn{Watcher(T0)}
        Print("main waits for w1: {T0.Await()}")
        W.Await()
    E := spawn{Echo(7)}
    F := spawn{Echo("seven")}
    Print("{E.Await()} {F.Await()}")
    R := sync:
        block:
            X := spawn{Slow("in arm", 1.0)}
            X.Await()
        Slow("arm two", 0.5)
    Print("{R(0)} {R(1)}")
    spawn{Forever()}
    Sleep(2.5)
    Print("main ends")
