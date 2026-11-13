# expect: closes no block comment
# (the markers of block comments count in a # comment too, as in the Book of
# Verse's tests of the lexical grammar, TimSyntax.versetest)
Main():void =
    Print("x") # #> 
