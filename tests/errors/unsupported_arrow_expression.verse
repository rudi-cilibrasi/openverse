# expect: a lambda (…) => … is a nested function, which openverse does not have (#492
# A lambda parses (the Book of Verse tests, Literals/Function.versetest) and is refused.
Main():void =
    X := 7
    F := (X) => X + 1
    Print(F(X))
