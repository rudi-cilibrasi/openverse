# A spawn survives its creator; the command-line host ends with Main.
Finish()<suspends>:void=
    Print("spawn started")
    Sleep(0.0)
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
