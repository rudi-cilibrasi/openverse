# expect: 7:13: this call may signal an event (Walk → event.Signal) in a failure context, which --signal-no-rollback refuses
# (#515, #283) under --signal-no-rollback, a Signal in the code after a recursive
# call of a function with several values (a return frame): it runs on each
# value inside the condition that takes it
Walk(E:event(int), N:int)<transacts><decides>:int =
    N > 0
    X := Walk[E, N - 1] | N
    E.Signal(X)
    X + 1
Main()<suspends>:void =
    E := event(int){}
    if (V := Walk[E, 2], V > 100) then Print("no")
