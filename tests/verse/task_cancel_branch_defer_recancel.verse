# the #261 loop for a branch: A's branch awaits a cancelled task (the
# scheduler cancels the branch alone, A not running); the branch's defer
# starts (through an immediate function) a task whose first run cancels A,
# which is waiting: A unwinds at once, and its exit stops its branches,
# among them this one, which is still unwinding (its wrapper is marked done
# only after its cancel). Expected: branch defer once, then A defer,
# killer done, end.
W()<suspends>:int =
    Sleep(9.0)
    1
Killer(T:task(int))<suspends>:void =
    T.Cancel()
    Print("killer done")
StartKiller(T:task(int)):void =
    spawn{Killer(T)}
A(Me:event(task(int)), Wt:task(int))<suspends>:int =
    defer:
        Print("A defer")
    T := Me.Await()
    branch:
        defer:
            Print("branch defer")
            StartKiller(T)
        Sleep(0.2)
        Wt.Await()
    Sleep(1.0)
    Print("never")
    1
Main()<suspends>:void =
    Wt := spawn{W()}
    Wt.Cancel()
    Me := event(task(int)){}
    S := spawn{A(Me, Wt)}
    Me.Signal(S)
    Sleep(2.0)
    Print("end")
