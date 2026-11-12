# expect: 9:12: this call may signal an event (Note → event.Signal) in a failure context, which --signal-no-rollback refuses
# (#515) under --signal-no-rollback, an event's Signal, through a function,
# in an if's condition: refused before the program runs
Note(E:event(int), N:int):int =
    E.Signal(N)
    N
Main():void =
    E := event(int){}
    if (Note(E, 1) > 0):
        Print("signalled")
