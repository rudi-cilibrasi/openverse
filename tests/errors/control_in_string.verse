# expect: 4:13: character U+0001 is not allowed in Verse source
# Control characters are rejected anywhere, including inside a string literal.
Main():void =
    Print("a  b")
