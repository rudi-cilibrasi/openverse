# Main awaiting a cancelled task waits for ever (the Book's API, task, Await:
# "a cancelled task never resumes its awaiters"): once no task can run, the
# program ends as a Main that waits with no task able to run does, as Err()
# does (exit 2), and Main's defer does not run
W()<suspends>:int =
    Sleep(10.0)
    1
Stopper(T:task(int))<suspends>:void =
    Sleep(1.0)
    T.Cancel()
Main()<suspends>:void =
    defer:
        Print("main unwound")
    T := spawn{W()}
    spawn{Stopper(T)}
    Print("got {T.Await()}")
    Print("never")
