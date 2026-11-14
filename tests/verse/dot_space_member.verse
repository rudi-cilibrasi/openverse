# A '.' and its member may have spaces between them, and a comment before
# the '.' (Book of Verse tests, ReserveDotSpace.versetest 3-7); separators
# between a class's members in braces (ClassBlockClause.versetest 18-20).
c := class{F:int = 1; G:int = 2, block{Print("made")}}
Main():void =
    O := c{}
    Print("{O. F} {O<# G #>.G}")
