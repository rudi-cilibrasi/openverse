# expect: an operand of '=' must be comparable, and wrapper is not
counter := class:
    N:int = 0
wrapper := struct:
    C:counter
Main():void =
    if (wrapper{C := counter{}} = wrapper{C := counter{}}) then Print("equal")
