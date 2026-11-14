# Awaiters run inside Signal (the Book's API, event's Signal; #513): a
# waiter whose task an earlier waiter of the same round cancels is not
# resumed at its turn; one that waits again inside the Signal joins the next
# round, so the second Signal reaches it and the third finds no one
Waiter(E:event(int), Tag:string, Delay:float, Times:int)<suspends>:void =
    Sleep(Delay)
    var I:int = 0
    loop:
        if (I >= Times) then break
        V := E.Await()
        Print("got {Tag} {V}")
        set I += 1
Killer(E:event(int), T:task(void), Delay:float)<suspends>:void =
    Sleep(Delay)
    V := E.Await()
    Print("got K {V}: cancel C")
    T.Cancel()
Main()<suspends>:void =
    E := event(int){}
    A := spawn{Waiter(E, "A", 0.3, 2)}
    C := spawn{Waiter(E, "C", 0.2, 1)}
    K := spawn{Killer(E, C, 0.1)}
    B := spawn{Waiter(E, "B", 0.0, 2)}
    Sleep(0.5)
    E.Signal(1)
    Print("between")
    Sleep(0.1)
    E.Signal(2)
    E.Signal(3)
    A.Await()
    B.Await()
    K.Await()
