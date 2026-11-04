# char8 code-unit literals 0oHH: one or two hex digits (not octal) give that
# UTF-8 code unit as a char.

Show(C:char):string = "[{C}]"

Main():void =
    A:char = 0o41
    if (A = 'A') { Print("0o41 is 'A'") }
    if (0o6a = 'j', 0o6A = 'j', 0o7e = '~', 0o20 = ' ') { Print("either case of hex digit") }
    # a single digit is the code unit itself: 0o9 is a tab, 0oa a newline
    Print(Show(0o9))
    if (0o9 = '\t', 0o09 = '\t', 0oa = '\n', 0o0 = 0o00) { Print("one or two digits") }
    # code units of a multi-byte UTF-8 sequence: U+00E9 is C3 A9
    E:string = array{0oc3, 0oa9}
    Print("caf{E} has {E.Length} chars")
    if (0oFF > 0o80, 0o80 > 0o7F) { Print("code units order as numbers") }
    Hex:[]char = array{0o48, 0o65, 0o78}
    Print(Hex)
