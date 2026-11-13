# An and is a scope of its own (Book of Verse ch. 7: "e0 and e1 evaluates
# the entire expression in a new lexical scope"): a name the left operand
# defines is visible on the right, and neither side's names escape the and
Values:[]int = array{3, 0, 5}

Main():void =
    if ((X := Values[0]) and X > 2) then Print("first above 2")
    if ((X := Values[1]) and X > 2) then Print("second above 2") else Print("second not above 2")
    for (I := 0..2, (X := Values[I]) and X > 1) { Print("index {I}") }
    # (the right's value is the and's)
    if (Y := ((X := Values[2]) and X * 10)) then Print("{Y}")
    # (a choice on the left, each of its values seen on the right, #283)
    for (Y := ((X := (1 | 2 | 3)) and (X > 1 and X))) { Print("choice {Y}") }
    # (and nests: `A and B and C` is `(A and B) and C`, whose inner and's
    # names are its own, so the right one groups)
    if ((X := Values[0]) and ((Z := X + 1) and Z > 3)) then Print("nested")
