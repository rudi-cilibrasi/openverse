# expect: 11:37: this call may signal an event (Tell → event.Signal) in a failure context, which --signal-no-rollback refuses
# (#515, #283) under --signal-no-rollback, a Signal in a clause before a break in
# a condition with a choice: alternatives that fail before the break are
# rolled back
Tell(E:event(int), V:int)<transacts>:int =
    E.Signal(V)
    V
Main()<suspends>:void =
    E := event(int){}
    loop:
        if (X := 1 | 2 | 3, Y := Tell(E, X), Y > 1, break) then Print("never")
        break
