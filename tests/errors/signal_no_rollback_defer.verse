# expect: this call may signal an event (Note → event.Signal) in a failure context
# (#515) under --signal-no-rollback, a defer: in a block in an if's
# condition: the defer cannot fail, but it runs inside the condition, which
# rolls it back
Note(E:event(int), N:int):int =
    E.Signal(N)
    N
Main():void =
    E := event(int){}
    if (X := block{ defer{ Note(E, 1) }; 3 }, X > 5) then Print("no") else Print("else")
