# Follow-up (#724): Mod alone, with operands beyond 64 bits. Epic's native
# Quotient(:int,:int) stops with "Value exceeds the range of a 64 bit
# integer" for them (int-euclid-big). With D = 2^63 and N = -(3 D) - 1,
# OpenVerse prints "before mod", "mod D - 1"; that error in Mod would stop
# the session after "before mod".
Next(N:int)<computes>:int = N + 1

Main():void =
    D := Next(9223372036854775807)
    N := -(3 * D) - 1
    Print("OVPROBE before mod")
    if (R := Mod[N, D]):
        if (R = D - 1) then Print("OVPROBE mod D - 1") else Print("OVPROBE mod other")
    else:
        Print("OVPROBE mod failed")
