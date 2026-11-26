# (#208) A `for` whose body has several values has several values itself: one
# array for each way to pick a value from every iteration's body, the first
# iteration's choice varying slowest. This is the `for` of the Verse Calculus
# and of the Verse team's prototype (augustss/verse-semantics, test For7),
# whose results the first loops below are. Every alternative of every body
# runs once, when the `for` is reached; a body with no value leaves the `for`
# with none; a `for` with no iteration has one value, the empty array.
Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")
Twice(X:int)<computes>:int = (X | X + 10)
Rows()<computes><decides>:[]int = for (X := (1 | 2)) { X | X + 10 }
Outer()<computes><decides>:[]int = for (A := Rows[], X : A) { X | 0 - X }
c := class:
    M(X:int)<computes><decides>:[]int = for (I : array{X, X + 1}) { I | 0 }
Main():void =
    for (A := for (X := (1 | 2 | 3)) { 4 | X }) { Print("[{Show(A)}]") }
    for (A := for (X := (1 | 2)) { X | X + 10 }) { Print("header choice: [{Show(A)}]") }
    if (A := for (X := (1 | 2)) { X | X + 10 }, A[0] > 5) then Print("first: [{Show(A)}]")
    for (A := for (X : array{1, 2}) { Twice(X) }) { Print("call: [{Show(A)}]") }
    for (A := Rows[]) { Print("function: [{Show(A)}]") }
    for (A := c{}.M[5]) { Print("method: [{Show(A)}]") }
    for (A := for (X : array{1, 2}) { X > 1 | X > 5 }) { Print("never") }
    for (A := for (X : array{1, 2, 3}) { if (X = 2) then (20 | 21) else X }) { Print("branch: [{Show(A)}]") }
    for (A := for (X : array{1}, X > 1) { X | 0 }) { Print("no iteration: {A.Length}") }
    for (A := for (X : array{1, 2}) { for (Y : array{X}) { Y | 7 } }, B : A) { Print("nested: [{Show(B)}]") }
    for (A := for (X : array{"a", "b"}) { X | "z" }) { Print("strings: {Join(A, "")}") }
    for (L := (for (X : array{1, 2}) { X | 9 }).Length + (1 | 2)) { Print("in an expression: {L}") }
    var Count:int = 0
    for (A := Outer[]) { set Count += 1 }
    Print("a for over a for: {Count}")
    var N:int = 0
    for (A := for (X : array{1, 2}) { (set N += 1; X) | (set N += 10; 7) }) { Print("effects: [{Show(A)}] {N}") }
    set N = 0
    if (A := for (X : array{1, 2}) { (set N += 1; X) | (set N += 10; 7) }, A[0] = 7) then Print("effects, first: [{Show(A)}] {N}")
