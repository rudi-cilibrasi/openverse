# The conversions of chars and code points (the Book's Runtime API, "char and
# char32"): C.ToCodeUnit() of a char, 0 to 255; C.ToCodePoint() of a char32;
# N.ToChar[] of an int, failing outside 0 to 255; N.ToChar32[], failing on a
# negative, a surrogate or above 0x10FFFF; C.ToAsciiChar32[] of a char,
# failing above 127; C.ToAsciiString() of a char32, its UTF-8 bytes.
Main():void =
    var Count:int = 0
    for (I := 0..255, C := I.ToChar[], C.ToCodeUnit() = I):
        set Count += 1
    var Units:int = 0
    for (C : "Aé"):
        set Units = Units * 256 + C.ToCodeUnit()
    var Points:[]int = array{}
    for (N : array{-1, 0, 65, 0xD7FF, 0xD800, 0xDFFF, 0xE000, 0x10FFFF, 0x110000}):
        if (P := N.ToChar32[]) then set Points += array{P.ToCodePoint()}
    var Shown:string = ""
    for (P : Points):
        set Shown += " {P}"
    if:
        not (-1).ToChar[]
        not 256.ToChar[]
        A := 'z'.ToAsciiChar32[]
        not 0o80.ToAsciiChar32[]
    then:
        Print("{Count} {Units} [{Shown} ] {A.ToCodePoint()} {0u1F600.ToAsciiString().Length} {0u4E2D.ToAsciiString()}")
