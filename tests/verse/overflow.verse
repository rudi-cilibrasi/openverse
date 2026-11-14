# int is 64-bit; leaving the range is a runtime error, not a failure (BPVM semantics).
Main():void =
    var I:int = 1
    loop:
        set I = I * 3
        if (I > 1000000000000000000) { Print("{I}") }
        # (never taken: the loop ends at the overflow; a loop needs a way
        # out, Book of Verse tests, Break.versetest)
        if (I = 0) { break }
