# An int past 64 bits is an int (the Verse VM's, #724), but ToString of it is
# a runtime error, not a failure: the third value printed ends the program.
Main():void =
    var I:int = 1
    loop:
        set I = I * 3
        if (I > 1000000000000000000) { Print("{I}") }
        # (never taken: the loop ends at the third print; a loop needs a way
        # out, Book of Verse tests, Break.versetest)
        if (I = 0) { break }
