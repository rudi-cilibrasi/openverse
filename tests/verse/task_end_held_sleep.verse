# Inside a task's end, as inside a Signal, only its awaiters go on: an arm
# whose sleep expired at the same tick keeps its turn in the scheduler's
# pass (the Book's API, Sleep: "resumption is driven by the world's timer
# manager"). Both's arm 1 goes on inside Work's end; Other, after Work in
# the pass, wakes; then Both's turn, where its arm 2 goes on.
Work()<suspends>:int =
    Sleep(0.1)
    Print("work ends")
    5
Other()<suspends>:void =
    Sleep(0.1)
    Print("other wakes")
Both(T:task(int))<suspends>:void =
    sync:
        Print("arm 1 got {T.Await()}")
        block:
            Sleep(0.1)
            Print("arm 2 wakes")
Main()<suspends>:void =
    T := spawn{Work()}
    spawn{Other()}
    spawn{Both(T)}
    Sleep(0.5)
    Print("end")
