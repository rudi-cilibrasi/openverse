Main():void = # a UTF-8 byte order mark comes before Main, which is still at column 0
    Print("a byte order mark at the start of a file is skipped")
    Print("café: other UTF-8 in strings is kept")
