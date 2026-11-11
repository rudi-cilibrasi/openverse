base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("base")
ib := class(base(int)):
    Go<override>(?N:int=block{branch{Print("default branch")};3})<suspends>:void=
        Print("body {N}")
        Sleep(0.01)
        Print("done")
Start(P:base(t) where t:type):task(void)=spawn{P.Go()}
StartAsync(P:base(t) where t:type)<suspends>:task(void)=spawn{P.Go()}
Main()<suspends>:void=
    A:=Start(ib{})
    Print("spawned immediate")
    A.Await()
    B:=StartAsync(ib{})
    Print("spawned async")
    B.Await()
