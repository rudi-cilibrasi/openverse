# expect: 4:38: unknown identifier 'X'
# An and is a scope of its own (Book of Verse ch. 7): X from the left is visible on the right, but not after the and.
Main():void =
    if ((X := 1) and X > 0) { Print("{X}") }
