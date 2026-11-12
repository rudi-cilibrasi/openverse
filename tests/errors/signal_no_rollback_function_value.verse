# expect: 15:13: this call may signal an event (Apply → loud.Shout (called as a function value) → event.Signal) in a failure context
# (#515) under --signal-no-rollback, a function value's call counts as a call
# of every function of its type given as a value (conservatively): Apply's
# call in the if's condition is refused, though this one passes Quiet
loud := class:
    E:event(int)
    Shout(N:int):int =
        E.Signal(N)
        N
Quiet(N:int):int = N
Apply(F:type{_(:int):int}, N:int):int = F(N)
Main():void =
    L := loud{E := event(int){}}
    Print("{Apply(L.Shout, 1)}")
    if (Apply(Quiet, 2) > 0) then Print("quiet")
