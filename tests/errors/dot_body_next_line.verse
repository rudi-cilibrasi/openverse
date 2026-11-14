# expect: 4:15: what follows a '.' must be on its line, with no comment between
# A '.' body is an expression on the line of its '.', not an indented block.
Main():void =
    if (1 < 2).
        Print("x")
