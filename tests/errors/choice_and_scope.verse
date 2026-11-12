# expect: 4:25: unknown identifier 'X'
# Each operand of and is its own scope, with a choice in it too (#283): X from the left is not visible on the right.
Main():void =
    if ((X := 1 | 2) and X > 1) { Print("x") }
