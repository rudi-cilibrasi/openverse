# expect: 7:39: this call may signal an event (event.Signal) in a failure context, which --signal-no-rollback refuses
# (#515, #283) under --signal-no-rollback, a Signal in the defer: of a block with
# a choice of its own in a condition: it runs as each value leaves the block
Main()<suspends>:void =
    E := event(int){}
    loop:
        if (X := block{ defer: E.Signal(1); Y := 1 | 2; Y * 10 }, X > 50) then Print("no")
        break
