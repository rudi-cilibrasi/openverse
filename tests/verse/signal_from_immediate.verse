# A Signal from code that is not <suspends> resumes its awaiters inside it
# too (the Book's tests signal from an assertion's body and check the
# awaiters' effects on the next line)
Listen(E:event(int))<suspends>:void =
    V := E.Await()
    Print("listener got {V}")
    W := E.Await()
    Print("listener got {W}")
Fire(E:event(int), X:int):void =
    E.Signal(X)
    Print("fired {X}")
Main():void =
    E := event(int){}
    spawn{Listen(E)}
    Fire(E, 1)
    Fire(E, 2)
    Print("main ends")
