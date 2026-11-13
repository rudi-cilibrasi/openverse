# Commas in a block make a tuple, semicolons and new lines a sequence (the
# Book of Verse, ch. 1, "Semicolons vs Commas"; SemicolonsVsCommas.versetest
# 70, 95, 100)
Pair():tuple(float, int) = {1.0, 2}
Last():int = {1; 2}
Main():void =
    # the line after `:=`: a tuple
    Value :=
        1, 2, 3
    Print("value {Value(0)} {Value(2)}")
    # option{} of a tuple, and of the last of a sequence
    if (P := option{1, 2}?, Q := option{1; 2}?) then Print("option {P(1)} {Q}")
    # a for's body: an array of tuples
    R := for (X := 1..2) { 3, X }
    if (S := R[1]) then Print("for {R.Length} {S(0)} {S(1)}")
    Print("pair {Pair()(1)} last {Last()}")
    # definitions joined by commas are the block's definitions
    block:
        X:int = 4, Y:int = 5
        Print("defs {X + Y}")
    # definitions and values: each definition visible after it, the group a tuple
    if (T := option{V := 3, V > 0, V + 1}?) then Print("mixed {T(0)} {T(1)} {T(2)}")
    var N:int = 1
    U := (block{var M:int = N, set M = 7, M})
    Print("var {U(0)} {U(1)} {U(2)}")
    # logic{} of a tuple of queries
    if (logic{true?, true?}?) then Print("logic")
