# expect: 4:4: c.Signal has several values, but Signal is also the name of a field, an enumerator, a member of a built-in type
c := class:
    K : int
    Signal(A : int)<transacts>:int = K | A
W(E : event(int))<suspends>:void =
    V := E.Await()
    Print("got {V}")
Main()<suspends>:void =
    E := event(int){}
    spawn{W(E)}
    Sleep(0.0)
    E.Signal(7)
    Sleep(0.0)
    for (X := c{K := 1}.Signal(9)):
        Print("{X}")
