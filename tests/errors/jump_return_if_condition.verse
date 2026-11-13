# expect: 4:23: return cannot leave a failure context
# A return in an if's condition (the Book of Verse's tests: Reachability.versetest:12, "Explicit return out of a failure context is not allowed", 3535)
F(X:int):int =
    if (X > 0, X < 10, return 1) then 2 else 3
Main():void = Print("{F(1)}")
