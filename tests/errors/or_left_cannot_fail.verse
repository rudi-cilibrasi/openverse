# expect: the left operand of or cannot fail
# The left operand of or must be able to fail, as not's must (the Book of Verse's tests, LogicalOr.versetest:143, error 3513).
F():int = 0
Main():void =
    X := F() or 1
    Print("{X}")
