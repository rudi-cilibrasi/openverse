# expect: expected tuple(), found int
# tuple() is the type of the empty value alone, not void, which takes any
# value (Book of Verse ch. 2; Tests/Void.versetest refuses a tuple() of (1, 2))
Main():void =
    X:tuple() = 1
