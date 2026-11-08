# a generic function may spawn a call that does not depend on its type parameters (#156)
Tick(Name:string, N:int)<suspends>:int =
    Sleep(N * 1.0)
    Print("{Name} ticked")
    N
Echo(X:t where t:type)<suspends>:t =
    T := spawn{Tick("helper", 1)}
    Sleep(0.5)
    Print("echo waits")
    T.Await()
    X
Main()<suspends>:void =
    Print(Echo("s"))
    Print("{Echo(7)}")
