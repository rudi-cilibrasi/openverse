# A flat inlined producer and the equivalent literal choice both undo
# their prefix effects when no row reaches the body.
Two(N:int):int = (Print("two {N}"); N) | N + 1
Main():void =
    var T:int = 0
    for (X := Two(1), (set T += 1; true?), Y := 3..X) { Print("y {X} {Y} {T}") }
    Print("call {T}")
    var U:int = 0
    for (X := (Print("one"); 1) | 2, (set U += 1; true?), Y := 3..X) { Print("y {X} {Y} {U}") }
    Print("choice {U}")
