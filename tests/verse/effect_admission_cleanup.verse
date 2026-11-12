cell := class:
    var N:int = 0
Tick(C:cell,Tag:string)<reads><writes>:void =
    set C.N += 1
    Print("{Tag} {C.N}")
Work(C:cell)<suspends><reads><writes>:void =
    defer:
        Tick(C,"cleanup")
    Tick(C,"begin")
    Sleep(0.1)
    Tick(C,"end")
Main()<suspends>:void =
    C := cell{}
    race:
        Work(C)
        block:
            Sleep(0.05)
            Print("cancel")
    Print("state {C.N}")
