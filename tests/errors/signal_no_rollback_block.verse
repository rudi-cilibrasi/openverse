# expect: 10:17: this construction may signal an event (loud's block → event.Signal) in a failure context
# (#515) under --signal-no-rollback, a construction in an if's condition
# runs the class's block:, which signals
loud := class:
    E:event(int)
    block:
        E.Signal(1)
Main():void =
    E := event(int){}
    if (L := loud{E := E}, 1 > 2) then Print("no") else Print("else")
