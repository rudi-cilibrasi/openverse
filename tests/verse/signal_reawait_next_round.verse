# An awaiter that awaits the same event again inside the Signal waits for
# the next one (the Book's API, event's Await: "lands the new registration
# in a fresh frame, so it waits for the next signal rather than the one in
# progress")
Echo(E:event(int))<suspends>:void =
    loop:
        V := E.Await()
        Print("echo {V}")
Main()<suspends>:void =
    E := event(int){}
    spawn{Echo(E)}
    E.Signal(1)
    Print("after 1")
    E.Signal(2)
    Print("after 2")
