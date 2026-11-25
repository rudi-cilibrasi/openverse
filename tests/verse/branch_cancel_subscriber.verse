# A function subscribed to an event, called by a Signal that a defer makes
# while a task is cancelled (#724): the cancelled task's child, a branch,
# signals in its defer, which runs before the task's own (Epic's Verse VM,
# UEFN 43.12, followup-conc/branch-cancel-order); the Signal resumes none of
# the cancelled task's waits, whose waits were cancelled first, and then
# calls the subscribed functions (Epic's Verse VM, followup-event/), which
# run as the code of the task that signalled: one cancels the subscription
# of another before its turn, and one signals a second event that a live
# task awaits, which goes on inside that Signal.
holder := class:
    var Victim:?cancelable = false
    Second:event(int)
    First(N:int):void =
        Print("first {N}")
        if (V := Victim?) then V.Cancel()
        Second.Signal(N + 10)
    Skipped(N:int):void = Print("skipped (wrong) {N}")
Child(E:event(int))<suspends>:void =
    branch:
        defer:
            Print("branch cleanup")
            E.Signal(1)
            Print("branch cleanup done")
        Sleep(10.0)
Task(E:event(int))<suspends>:void =
    defer:
        Print("task cleanup")
    Child(E)
    V := E.Await()
    Print("task resumed (wrong) {V}")
Watcher(F:event(int))<suspends>:void =
    V := F.Await()
    Print("watcher got {V}")
Main()<suspends>:void =
    E := event(int){}
    H := holder{Second := event(int){}}
    S1 := E.Subscribe(H.First)
    set H.Victim = option{E.Subscribe(H.Skipped)}
    spawn{Watcher(H.Second)}
    T := spawn{Task(E)}
    Sleep(0.1)
    T.Cancel()
    Print("cancelled")
    Sleep(0.1)
    Print("end")
