# expect: 7:13: this call may signal an event (Walk → event.Signal) in a failure context, which --signal-no-rollback refuses
# (#515, #283) under --signal-no-rollback, a Signal in the code after a call of
# itself that reaches a choice (choice points in sequence): it runs in the for's
# clause that takes each value, before the choice, as a continuation member's code
Walk(E:event(int), N:int)<transacts><decides>:int =
    N > 0
    X := Walk[E, N - 1] | N
    E.Signal(X)
    X | X + 100
Main()<suspends>:void =
    E := event(int){}
    for (V := Walk[E, 2]) { Print("{V}") }
