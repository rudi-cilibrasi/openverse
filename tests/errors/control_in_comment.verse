# expect: 3:23: character U+0007 is not allowed in Verse source
# Control characters are rejected anywhere, including inside a comment.
Main():void = # a bell  in a line comment
    Print("x")
