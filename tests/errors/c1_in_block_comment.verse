# expect: 4:13: character U+0085 is not allowed in Verse source
# C1 controls (U+0080 to U+009F) are rejected too, here NEL in a block comment.
Main():void =
    <# a NEL  #> Print("x")
