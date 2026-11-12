# expect: 5:9: 'X' is already defined; Verse does not allow shadowing
# An operand of and with a choice is a scope of its own, which cannot bind a name already in scope (#283).
Main():void =
    X := 5
    if ((X := 1 | 2) and 3 > 2) { Print("x") }
