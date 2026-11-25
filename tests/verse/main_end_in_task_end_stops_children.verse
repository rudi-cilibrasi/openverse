# Main ends inside the end of the task it awaited: its children are stopped
# there, before the task's later awaiters go on (#723).
Work()<suspends>:int =
    defer:
        Print("work defer")
    Sleep(0.2)
    7
Later(T:task(int))<suspends>:void =
    Sleep(0.1)
    V := T.Await()
    Print("later awaiter got {V}")
Loser()<suspends>:int =
    defer:
        Print("rush loser defer")
    Sleep(1.0)
    2
Main()<suspends>:void =
    T := spawn{Work()}
    spawn{Later(T)}
    R := rush:
        block:
            Sleep(0.0)
            1
        Loser()
    Print("rush = {R}")
    branch:
        defer:
            Print("branch defer")
        Sleep(1.0)
    V := T.Await()
    Print("main end {V}")
