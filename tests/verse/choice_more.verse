# choice (#208), the review's cases: in a for, an alternative whose own
# clauses succeed but whose later generators give no value is undone, as an
# if undoes it (the Book of Verse's rule: a for's clauses are one search, and
# nothing here reaches the body); set as the last clause of a macro; choices
# nested 30 deep in conditions (checked once each)
Main():void =
    var N:int = 0
    Xs := for (X := 1 | 2, (set N += 1; true?), (Print("p{X}"); true?), Y := 3 | 4, Y > 10) { Y }
    Print("for: {Xs.Length} values, N={N}")
    var M:int = 0
    if (X := 1 | 2, set M += 1, Print("q{X}"), Y := 3 | 4, Y > 10) then Print("yes") else Print("if: M={M}")
    Ys := for{set N = 7 | 8}
    Print("{Ys.Length} {N}")
    if (F := first{set N = 3 | 4; N > 3}) then Print("first {N}")
    if (Z := 1 | (if (Y29 := 0 | (if (Y28 := 0 | (if (Y27 := 0 | (if (Y26 := 0 | (if (Y25 := 0 | (if (Y24 := 0 | (if (Y23 := 0 | (if (Y22 := 0 | (if (Y21 := 0 | (if (Y20 := 0 | (if (Y19 := 0 | (if (Y18 := 0 | (if (Y17 := 0 | (if (Y16 := 0 | (if (Y15 := 0 | (if (Y14 := 0 | (if (Y13 := 0 | (if (Y12 := 0 | (if (Y11 := 0 | (if (Y10 := 0 | (if (Y9 := 0 | (if (Y8 := 0 | (if (Y7 := 0 | (if (Y6 := 0 | (if (Y5 := 0 | (if (Y4 := 0 | (if (Y3 := 0 | (if (Y2 := 0 | (if (Y1 := 0 | (if (Y0 := 0 | "s") then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then "a" else "b")) then Print("deep")
