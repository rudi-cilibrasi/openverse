# A statement or a clause whose value nothing takes is typed for Verse Core
# too (it infers a type there, or checks against void): an empty literal
# there, or an if whose branches are, gets the type it was elaborated at.
Tail():void = if (false?) then "" else ""
Count(N:int):int =
    for (I := 1..N):
        ""
        if (I = 2) then return I
    0
Main():void =
    ""
    if (false?) then "" else ""
    if (true?) then ""
    Tail()
    block:
        defer:
            Print("deferred")
            ""
        Print("block")
    var I:int = 0
    loop:
        set I += 1
        if (I > 2) then break
        ""
    for (J := 1..2) { "" }
    # (clauses: of an if, a for's filters, after a choice)
    if (true?, "") then Print("clause")
    for (J := 1..3, "" = "", J <> 2) { Print("filter {J}") }
    if (X := (1 | 2), "", X > 1) then Print("choice {X}")
    if (Y := first{Z := (1 | 2); ""; Z}) then Print("first {Y}")
    Print("{Count(3)} {I}")
