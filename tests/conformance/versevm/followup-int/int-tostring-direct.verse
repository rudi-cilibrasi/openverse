# Follow-up (#724): ToString called directly, not through interpolation, on
# an int beyond 64 bits. OpenVerse raises the overflow error after "in
# range", as Epic's Verse VM does ("Value exceeds the range of a 64 bit
# integer" in its native ToString(:int)).
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    S0 := ToString(Big - 1)
    if (S0 = "9223372036854775807") then Print("OVPROBE in range")
    S := ToString(Big)
    if (S.Length > 0) then Print("OVPROBE converted")
