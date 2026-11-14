# An awaiter that is cancelled, a race arm that loses, deregisters: the
# task's end does not resume it, and resumes the others (the Book's API,
# task, Await: "If the awaiting task is itself cancelled it deregisters
# automatically, so the completed task will not try to resume a dead
# caller"); the task goes on ("Awaiting is not owning").
Slow()<suspends>:int =
    Sleep(0.2)
    Print("slow ends")
    3
Main()<suspends>:void =
    T := spawn{Slow()}
    X := race:
        block:
            defer:
                Print("loser unwinds")
            V := T.Await()
            Print("never: the loser got {V}")
            V
        block:
            Sleep(0.1)
            9
    Print("race {X}")
    Print("main got {T.Await()}")
