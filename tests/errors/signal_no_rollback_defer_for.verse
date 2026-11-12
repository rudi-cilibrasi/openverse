# expect: this call may signal an event (subscribable_event.Signal) in a failure context
# (#515) under --signal-no-rollback, a for over two choices, whose body the
# compiler moves into a continuation of its own, in a defer: in an if's
# condition: the body runs inside the condition, so it is refused
Hear(X:int):void = Print("heard {X}")
Two(N:int):int = N | N + 1
Main():void =
    U := subscribable_event(int){}
    C := U.Subscribe(Hear)
    if (X := block{ defer{ R := for (A0 := (Two(0) | Two(2)), A1 := (Two(0) | Two(2)), A0 = 0) { U.Signal(A1); A1 } }; 3 }, X > 5) then Print("no") else Print("else")
