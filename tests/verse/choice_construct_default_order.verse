# Prefix defaults share their objects; trailing defaults and blocks run per value.
cell := class:
    var N:int = 0
MakeCell()<transacts>:cell =
    Print("new cell")
    cell{}
Tail()<transacts>:int =
    Print("tail")
    9
pack := class:
    X:int
    D:cell = MakeCell()
    Y:int
    T:int = Tail()
    block:
        set D.N += 1
        Print("block {X} {Y} cell {D.N}")
None()<decides>:int =
    false?
    0
Main():void =
    Ps := for (P := pack{X := 1 | 2, Y := 10 | 20}):
        Print("got {P.X} {P.Y} cell {P.D.N}")
        P
    for (P : Ps):
        Print("saved {P.X} {P.Y} cell {P.D.N}")
    if (P := pack{X := 1 | 2, Y := 10 | 20}, P.Y = 20):
        Print("first {P.X} {P.Y} cell {P.D.N}")
    # (D's default runs before Y's choice; neither alternative succeeds, so no
    # value reaches the body and the search undoes it, output too)
    Empty := for (P := pack{X := 0, Y := None[] | None[]}) { P }
    Print("empty {Empty.Length}")
