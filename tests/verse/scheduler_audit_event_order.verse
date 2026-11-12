# The later-started task waits first; the reference scheduler resumes A first.
Waiter(E:event(int),Tag:string,Delay:float)<suspends>:void=
    Sleep(Delay)
    Print("wait {Tag}")
    V:=E.Await()
    Print("got {Tag} {V}")
Main()<suspends>:void=
    E:=event(int){}
    A:=spawn{Waiter(E,"A",0.1)}
    B:=spawn{Waiter(E,"B",0.0)}
    Sleep(0.2)
    Print("signal")
    E.Signal(7)
    Print("returned")
    A.Await()
    B.Await()
