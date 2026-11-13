# expect: this for has no generator (X : A, or X := A..B) and its clauses cannot fail
# (X := binds the whole array: X : array{…} iterates over it; Book of Verse
# ch. 7, "For Without a Generator")
Main():void =
    for (X := array{1, 2, 3}) { Print("{X.Length}") }
