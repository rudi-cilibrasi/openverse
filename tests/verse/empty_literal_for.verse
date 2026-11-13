# A for's values, flattened over several generators, are inferred by Verse
# Core: a body that is an empty literal (or an if of them) gets the type it
# was elaborated at, wherever the for is.
Down(N:int):int = if (N > 0) then (N | Down(N - 1)) else 0
Main():void =
    Grid := for (I := 0..2, J := 0..1) { "" }
    Print("{Grid.Length}")
    Print("{(for (I := 0..2, J := 0..1) { if (false?) then "x" else "" }).Length}")
    Print("{(for (true?, I := 0..1, J := 0..1) { "" }).Length}")
    Print("{(for (I := 0..1, I > 0, J := 0..2) { "" }).Length}")
    # (an exclusive choice among the clauses, #314)
    Print("{(for (X := (if (true?) then (1 | 2) else 3), I := 1..2) { "" }).Length}")
    # (a recursive function with several values, taken lazily, #246)
    Print("{(for (X := Down(2), J := 1..2) { "" }).Length}")
    # (one generator, where the for's own type is inferred)
    Print("{(for (I := 1..3) { "" }).Length}")
    for (I := 0..1, J := 0..1) { "" }
    var Rows:[][]string = for (I := 0..1) { for (J := 0..2) { "" } }
    if (set Rows[1][2] = "x", A := Rows[1][2], B := Rows[0][2]) then Print("{A}[{B}]")
