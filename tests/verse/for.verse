# for expressions (Book of Verse ch. 7).
Main():void =
    Squares := for (X : array{1, 2, 3, 4, 5}, X > 2) { X * X }
    Print("squares of >2: {Squares.Length}")
    for (S : Squares) { Print("{S}") }
    Cells := for (X := 1..3, Y := 1..3):
        X * 10 + Y
    Print("cells: {Cells.Length}, first {Cells[0] or 0}, last {Cells[8] or 0}")
    Empty := for (N := 5..1) { N }
    Print("5..1 has {Empty.Length} elements")
    for (I -> C : "abc") { Print("{I}: {C}") }
    Pairs := for (X := 1..4, X <> 2, Y := X..4, X + Y = 5) { X * 100 + Y }
    for (P : Pairs) { Print("pair {P}") }
    var Total:int = 0
    for (X := 1..10, Mod[X, 3] = 0) { set Total += X }
    Print("sum of multiples of 3 up to 10: {Total}")
