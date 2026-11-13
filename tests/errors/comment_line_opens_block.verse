# expect: unterminated block comment
Main():void =
    Print("x") # a <# opens a block comment, which never ends
    Print("y")
