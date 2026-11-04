# expect: 4:14: the file is not valid UTF-8 (byte 0xFF)
# A source file must be UTF-8.
Main():void =
    Print("cafÿ")
