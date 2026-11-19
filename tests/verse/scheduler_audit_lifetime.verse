# A spawn survives its creator; the command-line host ends with Main.
# (#724: a branch and a rush's arm that goes on are children of the task whose
# code started them, stopped when that task ends, after its own defers: Epic's
# Verse VM, UEFN 43.12; no longer when the function that started them exits.)
Finish()<suspends>:void=
    Print("spawn started")
    Sleep(0.01)
    Print("spawn finished")
Never()<suspends>:void=
    defer:Print("pending task cleanup")
    Print("pending task started")
    Sleep(Inf)
Launch()<suspends>:task(void)=
    branch:
        defer:Print("branch cleanup")
        Print("branch started")
        Sleep(Inf)
    T:=spawn{Finish()}
    Print("creator leaving")
    T
Main()<suspends>:void=
    defer:Print("main cleanup")
    T:=Launch()
    Print("creator returned")
    T.Await()
    Pending:=spawn{Never()}
    Print("main ended")
