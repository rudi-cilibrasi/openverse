# expect: this call may signal an event (sticky_event.Signal) in a failure context, which the no_rollback effect of an event's Signal does not allow
# (#515) a sticky event's Signal in a <decides>
# function's body, whose failure would roll it back
Mark(S:sticky_event(int), N:int)<decides>:void =
    S.Signal(N)
    N > 0
Main():void =
    S := sticky_event(int){}
    if (Mark[S, 1]):
        Print("marked")
