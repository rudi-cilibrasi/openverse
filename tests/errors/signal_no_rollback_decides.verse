# expect: this call may signal an event (sticky_event.Signal) in a failure context, which --signal-no-rollback refuses
# (#515) under --signal-no-rollback, a sticky event's Signal in a <decides>
# function's body, whose failure would roll it back
Mark(S:sticky_event(int), N:int)<transacts><decides>:void =
    S.Signal(N)
    N > 0
Main():void =
    S := sticky_event(int){}
    if (Mark[S, 1]):
        Print("marked")
