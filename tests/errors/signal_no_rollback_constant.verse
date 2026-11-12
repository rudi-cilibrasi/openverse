# expect: 10:8: this use of the constant K may signal an event (K → Fresh → event.Signal) in a failure context
# (#515) under --signal-no-rollback, a use of a constant in an if's condition
# runs its initialiser, which signals
Fresh():int =
    E := event(int){}
    E.Signal(1)
    1
K:int = Fresh()
Main():void =
    if (K > 2) then Print("no") else Print("else")
