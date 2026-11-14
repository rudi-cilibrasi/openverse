# Each awaiter of a task gets its result, the same one, and an Await of a
# task that has ended gives it at once, without suspending (the Book's API,
# task, Await: "Returns immediately only when the task has already reached
# the completed phase"; ch. 14: "the result is sticky"): a race arm that
# awaits it ends at once and wins, and the arm after it never starts.
Make(X:int)<suspends>:int =
    Sleep(0.1)
    X * 2
Get(T:task(int), N:string)<suspends>:void =
    Print("{N} got {T.Await()}")
Main()<suspends>:void =
    T := spawn{Make(21)}
    spawn{Get(T, "a")}
    spawn{Get(T, "b")}
    Print("main got {T.Await()}")
    W := race:
        T.Await()
        block:
            Print("never starts")
            Sleep(0.1)
            0
    Print("race {W}")
    Print("again {T.Await()}")
