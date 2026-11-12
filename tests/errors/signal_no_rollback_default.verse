# expect: this call may signal an event (Note → event.Signal) in a failure context
# (#515) under --signal-no-rollback, a named parameter's default, taken by a
# call in a for's clause: it runs in the clause
Note(E:event(int), N:int):int =
    E.Signal(N)
    N
Two(E:event(int), ?N:int = Note(E, 1)):int = N | N + 1
Main():void =
    E := event(int){}
    for (X := Two(E), X > 5):
        Print("{X}")
