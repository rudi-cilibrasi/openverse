# Nested refining casts whose suspension is only visible inside the inner lift.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
ThenNested(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<suspends>:void =
    if (D := dup[P]):
        if (E := dup[Q]):
            Sleep(0.0)
            Print("nested then")
ElseNested(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<suspends>:void =
    if (D := dup[P]):
        Print("outer then")
    else if (E := dup[Q]):
        Sleep(0.0)
        Print("nested else")
# The else runs in the source function and owns the background task.
ElseOwner(P:pair(a, b) where a:type, b:type)<suspends>:void =
    if (D := dup[P]):
        Print("typed")
    else:
        branch:
            Sleep(1.0)
            Print("background")
        Sleep(0.0)
        Print("else done")
    Sleep(2.0)
    Print("caller done")
# Only the else suspends. The taken branch can update the shared slot.
ImmediateThen(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var Value:int = 0
    branch:
        Sleep(0.5)
        Print("observed {Value}")
    if (D := dup[P]):
        set Value = 7
        ()
    else:
        Sleep(1.0)
    Sleep(2.0)
Worker(Label:string)<suspends>:void =
    Sleep(1.0)
    Print(Label)
SpawnWithShared(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var Value:int = 0
    defer: Print("spawn cleanup {Value}")
    branch:
        Sleep(0.5)
        Print("spawn observed {Value}")
    if (D := dup[P]):
        set Value = 7
        spawn{Worker("spawn worker")}
    Sleep(2.0)
SpawnNested(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<suspends>:void =
    var Value:int = 0
    branch:
        Sleep(0.5)
        Print("nested spawn observed {Value}")
    if (D := dup[P]):
        set Value = 9
        if (E := dup[Q]):
            ()
        else:
            spawn{Worker("nested spawn worker")}
            ()
    Sleep(2.0)
CancelledWorker()<suspends>:void =
    defer: Print("worker cancelled")
    Sleep(1.0)
CancelWithShared(P:pair(a, b) where a:type, b:type)<suspends>:void =
    var Value:int = 0
    branch:
        Sleep(0.5)
        Print("cancel observed {Value}")
    T := spawn{CancelledWorker()}
    if (D := dup[P]):
        set Value = 7
        T.Cancel()
    Sleep(2.0)
Main()<suspends>:void =
    P := dup(int){A := 1, B := 2}
    Q := pair(int, string){A := 1, B := "q"}
    ThenNested(P, P)
    ElseNested(Q, P)
    ElseOwner(Q)
    ImmediateThen(P)
    SpawnWithShared(P)
    SpawnNested(P, Q)
    CancelWithShared(P)
