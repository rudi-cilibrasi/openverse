# A subscribed function starts a task that awaits the same event, while the
# Signal is calling the subscribed functions: does that Signal resume it?
# (Epic's API: "awaits registered during a signal ... are deliberately not
# resumed by that same signal"; the Verse VM resumes the awaiters before it
# calls the functions, UEFN 43.12, await-and-subscribe.)
# OpenVerse (#724) prints (the new awaiter waits for the next Signal, which
# resumes it before calling the function again; the function starts a task
# once):
#   handler 1 | after signal 1 | waiter 2 | handler 2 | after signal 2
# If the Signal that is running resumed it:
#   handler 1 | waiter 1 | after signal 1 | handler 2 | after signal 2
# (A refusal of the spawn in a subscribed function, or a runtime error
# there, would answer a different question: whether a subscribed function
# may start a task at all.)
starter := class:
    E:event(int)
    var Started:logic = false
    OnHandler(N:int):void =
        Print("OVPROBE handler {N}")
        if (not Started?):
            set Started = true
            spawn{Waiter(E)}

Waiter(E:event(int))<suspends>:void =
    V := E.Await()
    Print("OVPROBE waiter {V}")

Main()<suspends>:void =
    E := event(int){}
    K := starter{E := E}
    S := E.Subscribe(K.OnHandler)
    E.Signal(1)
    Print("OVPROBE after signal 1")
    Sleep(0.1)
    E.Signal(2)
    Print("OVPROBE after signal 2")
    Sleep(0.1)
    S.Cancel()
