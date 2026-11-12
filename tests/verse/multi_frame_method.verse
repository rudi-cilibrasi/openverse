# (#283) A method with several values whose call of itself has code after it,
# with Self kept in its frames; its clauses change a field.
counter := class:
    var Seen:int = 0
    Walk(N:int)<transacts><decides>:int =
        N > 0
        set Seen += 1
        X := Walk[N - 1] | N
        X * 2 + Seen
Main()<transacts>:void =
    C := counter{}
    for (V := C.Walk[3]) { Print("v {V} seen {C.Seen}") }
    if (V := C.Walk[2], V > 10) then Print("first {V} seen {C.Seen}")
    Print("seen {C.Seen}")
