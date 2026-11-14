counter := class { var N:int = 0 }
Pair(C:counter, Tag:string, N:int)<suspends>:tuple(int, int) =
    defer: Print("cleanup {Tag}")
    set C.N += 1
    Print("start {Tag} {C.N}")
    Sleep(0.1)
    set C.N += 1
    Print("end {Tag} {C.N}")
    (N, N + 1)

Main()<suspends>:void =
    C := counter{}
    A := Pair(C, "done", 1) + (3, 4)
    if (A = array{1, 2, 3, 4}) then Print("done {C.N}")
    race:
        block:
            B := (5, 6) + Pair(C, "cancel", 7)
            Print("wrong {B.Length}")
        Sleep(0.01)
    Print("cancelled {C.N}")
