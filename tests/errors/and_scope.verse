# expect: 4:21: unknown identifier 'X'
# Each operand of and is its own scope: X from the left is not visible on the right.
Main():void =
    if ((X := 1) and X > 0) { Print("x") }
