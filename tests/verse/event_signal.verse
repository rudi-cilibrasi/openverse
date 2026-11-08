# event(t): Signal wakes every task waiting at that moment, in the order they began, with the value; a Signal with no one waiting is lost; a wait in a losing race arm is cancelled (#156)
Listener(Name:string, E:event(int), N:int)<suspends>:void =
    var I:int = 0
    loop:
        if (I >= N) then break
        V := E.Await()
        Print("{Name} got {V}")
        set I += 1
Main()<suspends>:void =
    E := event(int){}
    E.Signal(0)
    A := spawn{Listener("a", E, 2)}
    B := spawn{Listener("b", E, 1)}
    Sleep(1.0)
    E.Signal(1)
    Print("signalled 1")
    Sleep(1.0)
    E.Signal(2)
    E.Signal(3)
    Print("signalled 2 and 3")
    A.Await()
    B.Await()
    Go := event(string){}
    W := spawn{Waiter(Go)}
    Sleep(0.5)
    Go.Signal("go")
    Print("main after signal")
    Print("waiter said {W.Await()}")
    Later()
Waiter(G:event(string))<suspends>:string =
    X := G.Await()
    Print("waiter woke with {X}")
    "ok {X}"
Timed(E:event(int))<suspends>:string =
    race:
        block:
            V := E.Await()
            "got {V}"
        block:
            Sleep(1.0)
            "timeout"
Later()<suspends>:void =
    E := event(int){}
    Print(Timed(E))
    E.Signal(9)
    T := spawn{Timed(E)}
    Sleep(0.5)
    E.Signal(10)
    Print(T.Await())
