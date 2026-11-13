# expect: 4:8: expected '(', '{', ':' or '.' after for, found 'X'
# A for's clauses are in parentheses, braces, or a ':' or '.' block.
Main():void =
    for X := 1..3:
        Print("x")
