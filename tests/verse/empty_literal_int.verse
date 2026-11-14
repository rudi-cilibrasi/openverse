# An empty array{} with no type from its context is an array of false, below
# every array type (Book of Verse tests, Array.versetest:90, String.versetest:181):
# compared with a string it is the empty string; with an int, a value of
# another type, the comparison fails ("Comparisons between different types
# still compile, but they always fail", ch. 4).
Main():void =
    if (array{} = 0) then Print("equal") else Print("an int is no array")
    if (array{} = "") then Print("the empty string")
