# The places the Book gives an effect among a for's clauses, where each
# filter can fail (Book of Verse ch. 7, "Each filter must be failable"; its
# tests, for.versetest 223-236, 317-392): a filter that pairs the effect
# with a check, (set T = E; true?); a definition's value; a generator's
# source; a call that can fail. What a failure undoes is the search's
c := class:
    var V:int = 0
    Bump(X:int)<transacts><decides>:int =
        set V += X
        X <> 2
        V
Main():void =
    var T:int = 0
    Xs:[]int = array{3, 4, 5}
    R1 := for (X := 1..2; E := Xs[X]; (set T = E; true?)) { X }
    Print("pair {R1.Length} {T}")
    var Seen:int = 0
    R2 := for (X := 1..3, Y := (set Seen += X; X * 10), Y > 10) { Y }
    Print("definition {R2.Length} {Seen}")
    var N:int = 0
    R3 := for (X := 1..(set N += 2; N)) { X }
    Print("source {R3.Length} {N}")
    C := c{}
    R4 := for (X := 1..3, C.Bump[X]) { X }
    Print("failable call {R4.Length} {C.V}")
