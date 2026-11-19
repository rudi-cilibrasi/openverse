# expect: 9:12: this call may signal an event (Note → event.Signal) in a failure context, which the no_rollback effect of an event's Signal does not allow
# (#515) an event's Signal, through a function,
# in an if's condition: refused before the program runs
Note(E:event(int), N:int):int =
    E.Signal(N)
    N
Main():void =
    E := event(int){}
    if (Note(E, 1) > 0):
        Print("signalled")
