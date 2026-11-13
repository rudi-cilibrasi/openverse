# expect: 5:8: expected an expression after '.', on its line
# A '.' body is an expression on the line of its '.', not an indented block.
Main():void =
    if (1 < 2).
        Print("x")
