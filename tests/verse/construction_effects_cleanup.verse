cell:=class<allocates>:
    var N:int=0
    var Made:int=0
ticket:=class<transacts>:
    Cell:cell
    Value:int
    block:
        set Cell.Made+=1
        Print("make {Value} {Cell.Made}")
Pick(C:cell,N:int)<transacts><decides>:int=
    T:=ticket{Cell:=C,Value:=N}
    set C.N+=T.Value
    N>1
    C.N
Work(C:cell)<suspends><transacts>:void=
    T:=ticket{Cell:=C,Value:=5}
    defer:
        set C.N+=T.Value
        Print("cleanup {C.N} {C.Made}")
    Print("work {T.Value}")
    Sleep(0.1)
Main()<suspends>:void=
    C:=cell{}
    if(X:=Pick[C,1]):Print("bad {X}")
    Print("rollback {C.N} {C.Made}")
    if(X:=Pick[C,2]):Print("keep {X} {C.Made}")
    race:
        Work(C)
        block:
            Sleep(0.05)
            Print("cancel")
    Print("state {C.N} {C.Made}")
