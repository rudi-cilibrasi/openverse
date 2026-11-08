# T.Cancel() unwinds a task (its defers run); awaiting a cancelled task cancels the awaiting task; a task cancelling itself stops at its next wait; a done task is not changed (#156)
Worker(Name:string)<suspends>:int =
    defer:
        Print("{Name} unwound")
    var I:int = 0
    loop:
        Sleep(1.0)
        set I += 1
        Print("{Name} {I}")
    I
Waiter(T:task(int))<suspends>:void =
    defer:
        Print("waiter unwound")
    Print("waiter got {T.Await()}")
Quick()<suspends>:int = 5
SelfStop(Me:event(task(int)))<suspends>:int =
    T := Me.Await()
    T.Cancel()
    Print("still running until it waits")
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    W := spawn{Worker("w")}
    A := spawn{Waiter(W)}
    Sleep(2.5)
    W.Cancel()
    Print("cancelled w")
    Sleep(1.0)
    Q := spawn{Quick()}
    Q.Cancel()
    Print("quick still gives {Q.Await()}")
    Me := event(task(int)){}
    S := spawn{SelfStop(Me)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
