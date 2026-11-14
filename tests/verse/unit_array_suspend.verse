counter := class:
    var Ticks:int = 0

Empty(C:counter, Tag:string)<suspends>:void =
    defer: Print("cleanup {Tag}")
    set C.Ticks += 1
    Print("start {Tag} {C.Ticks}")
    Sleep(0.1)
    set C.Ticks += 1
    Print("end {Tag} {C.Ticks}")

Main()<suspends>:void =
    C := counter{}
    A:[]int = Empty(C, "done")
    Print("done {A.Length} {C.Ticks}")
    race:
        block:
            B:[]string = Empty(C, "cancel")
            Print("wrong {B.Length}")
        Sleep(0.01)
    Print("cancelled {C.Ticks}")
