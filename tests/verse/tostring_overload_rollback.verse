counter := class:
    var Count:int = 0

ToString(C:counter)<transacts>:string =
    set C.Count += 1
    Print("converted {C.Count}")
    "count {C.Count}"

Main():void =
    C := counter{}
    Print("first {C}")
    if (Discard := "rolled back {C}", false?):
        Print(Discard)
    Print("after {C.Count}")
    Print("again {C}")
