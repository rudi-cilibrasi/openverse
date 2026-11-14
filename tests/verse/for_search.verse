# What a for undoes (the Book of Verse's rule, FlowControl/for.versetest 317-392,
# Range.versetest 140, 159, SoftwareTransactionalMemory.versetest 74-88): its
# clauses are one search; reaching the body keeps what the search did since the
# last success, a failure undoes back to the element or alternative being tried,
# and the search's end undoes what it did since the last success.
c := class:
    var V:int
    Inc()<transacts>:int =
        set V = V + 1
        V
    Fail()<transacts><decides>:int =
        set V = V + 1
        V < 0
        V

Main()<transacts>:void =
    # a source's effect stays when some element reaches the body (for.versetest:330)
    X1 := c{V := 1}
    R1 := for (I := 1..X1.Inc(), I <> 1) { I }
    Print("kept {R1.Length} {X1.V}")
    # and is undone when none does (:344)
    X2 := c{V := 1}
    R2 := for (I := 1..X2.Inc(), I > 2) { I }
    Print("undone {R2.Length} {X2.V}")
    # an inner source for an outer element whose inner search finds nothing (:362)
    X3 := c{V := 2}
    Y3 := c{V := 2}
    R3 := for (I := 1..X3.Inc(), J := 1..Y3.Inc(), I <> 2) { 10 * I + J }
    Print("inner {R3.Length} {X3.V} {Y3.V}")
    # the first generator's source and the clauses before it (Range.versetest:140)
    var A:int = 1
    var N:int = 0
    for ((set N += 1; true?), J : array{(set A = 5)}, K := J..2) { Print("never") }
    Print("before {A} {N}")
    # an outer generator's filters, undone for an element with no value below
    var T:int = 0
    for (I := 1..3, (set T += 10 * I; true?), (Print("i {I}"); true?), J := 2..I) { Print("body {I} {J} {T}") }
    Print("filters {T}")
    # a choice of values is one more generator (#208), its alternative's own code
    # undone with it; a parenthesized choice is spliced in; a choice in an expression
    var M:int = 0
    for (Y := (Print("a"); 1) | ((set M += 5; 2) | 3), (set M += 1; true?), Z := 2..Y) { Print("ch {Y} {Z} {M}") }
    for (Y := 10 + (0 | 1), (set M += 100; true?), Z := 11..Y) { Print("ex {Y} {Z} {M}") }
    Print("choice {M}")
    # a var of the clauses is the search's too
    for (I := 1..3, var W:int = I, (set W += 1; true?), K := 4..W) { Print("w {I} {W} {K}") }
    # an effect before the second generator only, a third with none before it
    # (searched inside the second's probe, and also entered outside one)
    var Q:int = 0
    for (I := 1..3, (set Q += 1; true?), J := 2..I, K := J..3, K <> 3 or J = 3) { Print("q {I} {J} {K} {Q}") }
    Print("q {Q}")
    # maps, strings and indices as generators
    Mp:[int]int = map{1 => 10, 2 => 20}
    var S:int = 0
    for (Key -> Val : Mp, (set S += Val; true?), Ch : "ab", Key = 2) { Print("m {Key} {Ch} {S}") }
    for (Ix -> C2 : "xyz", (set S += 1; true?), Ix > 1) { Print("s {Ix} {C2} {S}") }
    Print("map {S}")
    # a body that fails fails the for, and the if around it undoes it all
    X4 := c{V := 0}
    if (for (I := 0..X4.Inc(), J := 0..I) { I < 1 }) then Print("no") else Print("body fails {X4.V}")
    # a failing source, alone and after an element (SoftwareTransactionalMemory.versetest:88)
    X5 := c{V := 0}
    R5 := for (I := X5.Inc()..X5.Inc(), V := X5.Fail[]) { V }
    Print("fail {R5.Length} {X5.V}")
