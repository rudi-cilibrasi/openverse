# spawn of a method with several implementations (#173): the task runs
# the dispatch on the receiver's class
agent := class:
    Name:string
    Run(N:int)<suspends>:int =
        Sleep(1.0)
        Print("{Name} ran {N}")
        N
fast := class(agent):
    Run<override>(N:int)<suspends>:int =
        Print("{Name} fast {N}")
        N * 2
slow := class(agent):
    Run<override>(N:int)<suspends>:int =
        defer:
            Print("{Name} unwinds")
        Sleep(5.0)
        Print("{Name} slow {N}")
        N * 3
Main()<suspends>:void =
    As:[]agent = array{agent{Name := "a"}, fast{Name := "f"}, slow{Name := "s"}}
    var Ts:[]task(int) = array{}
    for (A : As):
        set Ts += array{spawn{A.Run(Ts.Length + 1)}}
    var Total:int = 0
    for (T : Ts):
        set Total += T.Await()
    Print("total {Total}")
    S := spawn{slow{Name := "c"}.Run(9)}
    Sleep(1.0)
    S.Cancel()
    # cancelling a dispatched task unwinds the implementation that runs
    X:agent = slow{Name := "d"}
    S2 := spawn{X.Run(4)}
    Sleep(1.0)
    S2.Cancel()
    Print("end")
