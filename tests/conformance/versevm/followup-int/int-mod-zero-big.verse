# Follow-up (#724): Mod of a dividend beyond 64 bits by zero. Epic's native
# Quotient stops for Quotient[2^63, 0] with "Value exceeds the range of a 64
# bit integer" (int-div-zero-big), not with a failure. OpenVerse fails, as
# for any int, and prints "before mod", "mod failed"; that error in Mod
# would stop the session after "before mod".
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("OVPROBE before mod")
    if (Mod[Big, 0]) then Print("OVPROBE mod succeeded") else Print("OVPROBE mod failed")
