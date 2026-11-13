# expect: 4:42: unknown identifier 'X'
# An and is a scope of its own, with a choice in it too (#283): X from the left is visible on the right, but not after the and.
Main():void =
    if ((X := 1 | 2) and X > 1) { Print("{X}") }
