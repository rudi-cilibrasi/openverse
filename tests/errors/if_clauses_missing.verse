# expect: 5:4: expected the clauses of if after ':'
# `if:` takes an indented block of clauses, which may not be empty.
Main():void =
    if:
    Print("x")
