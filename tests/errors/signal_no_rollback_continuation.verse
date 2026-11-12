# expect: this call may signal an event (Note → event.Signal) in a failure context, which --signal-no-rollback refuses
# (#515) under --signal-no-rollback, a for clause after two choices, which
# the compiler moves into a continuation of its own: still the for's clause,
# so still refused
Two(N:int):int = N | N + 1
Note(E:event(int), N:int):int =
    E.Signal(N)
    N
Main():void =
    E := event(int){}
    for (X := (Two(0) | Two(2)), Y := (Two(0) | Two(2)), Note(E, X) = 0):
        Print("{X} {Y}")
