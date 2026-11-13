Twice(E:event(int),Tag:string)<suspends>:void=
    V:=E.Await()
    Print("first {Tag} {V}")
    W:=E.Await()
    Print("second {Tag} {W}")
Main()<suspends>:void=
    E:=event(int){}
    A:=spawn{Twice(E,"A")}
    B:=spawn{Twice(E,"B")}
    E.Signal(1)
    E.Signal(2)
    Print("sent one two")
    Sleep(0.01)
    E.Signal(3)
    Print("sent three")
    A.Await()
    B.Await()
    Print("done")
