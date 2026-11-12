# expect: 18:16: this call may signal an event (loud.Notify → subscribable_event.Signal) in a failure context
# (#515) under --signal-no-rollback, an interface method whose implementation
# signals, called in an if's condition: a dispatch counts as a call of every
# implementation
notifier := interface:
    Notify(N:int):int
loud := class(notifier):
    E:subscribable_event(int)
    Notify<override>(N:int):int =
        E.Signal(N)
        N
quiet := class(notifier):
    Notify<override>(N:int):int = N
Pick(L:logic, E:subscribable_event(int)):notifier = if (L?) then loud{E := E} else quiet{}
Main():void =
    E := subscribable_event(int){}
    N := Pick(false, E)
    if (N.Notify(1) > 0):
        Print("notified")
