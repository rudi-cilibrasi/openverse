# What a for undoes: the Book of Verse's rule holds for a for whose generators
# are over ranges, arrays, maps and strings and choices of values (for_search).
# A for with a call of a function with several values in its clauses keeps,
# for now, the old rule (docs/LANGUAGE.md, "Choice"): what a generator's
# clauses did stays once they succeed, even when no value after them reaches
# the body. This test pins that boundary.
Two(N:int):int = (Print("two {N}"); N) | N + 1
Main():void =
    var T:int = 0
    for (X := Two(1), (set T += 1; true?), Y := 3..X) { Print("y {X} {Y} {T}") }
    Print("call {T}")
    var U:int = 0
    for (X := (Print("one"); 1) | 2, (set U += 1; true?), Y := 3..X) { Print("y {X} {Y} {U}") }
    Print("choice {U}")
