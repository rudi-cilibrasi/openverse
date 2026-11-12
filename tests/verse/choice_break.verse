# A break in the clauses of an if with a choice leaves the loop (#283).
Main():void =
    loop:
        if (X := 1 | 2, break) then Print("x")
        break
    Print("left the loop")
