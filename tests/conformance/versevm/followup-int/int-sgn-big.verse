# Follow-up (#724): Sgn of an int beyond 64 bits. Epic's Min and Max take
# such ints (int-intrinsics-big: "min max"); its native Clamp stops with
# "Value exceeds the range of a 64 bit integer". OpenVerse prints "before
# sgn", "sgn -1"; that error in Sgn would stop the session after "before sgn".
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("OVPROBE before sgn")
    if (Sgn(-Big - 1) = -1) then Print("OVPROBE sgn -1") else Print("OVPROBE sgn other")
