# Follow-up (#724): Abs of an int beyond 64 bits. Epic's Abs gives 2^63 for
# -2^63 (book-int-abs-min), an argument inside 64 bits; its native Quotient
# and Clamp stop with "Value exceeds the range of a 64 bit integer" for an
# argument beyond them. OpenVerse prints "before abs", "abs 2^63 + 1"; that
# error in Abs would stop the session after "before abs".
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("OVPROBE before abs")
    if (Abs(-Big - 1) = Big + 1) then Print("OVPROBE abs 2^63 + 1") else Print("OVPROBE abs other")
