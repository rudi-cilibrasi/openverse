# Follow-up (#724): Euclidean Quotient and Mod, and Floor and Ceil of a
# quotient, with operands beyond 64 bits. With D = 2^63 and N = -(3 D) - 1,
# OpenVerse prints "quotient -4", "mod D - 1", "floor -4", "ceil -3". Epic's
# Verse VM stops at the first: its native Quotient(:int,:int) raises "Value
# exceeds the range of a 64 bit integer", a known difference (int-mod-big
# asks about Mod alone; Floor and Ceil of such a quotient work there,
# int-rational-big).
Next(N:int)<computes>:int = N + 1

Main():void =
    D := Next(9223372036854775807)
    N := -(3 * D) - 1
    if (Q := Quotient[N, D], Q = -4) then Print("OVPROBE quotient -4") else Print("OVPROBE quotient other")
    if (R := Mod[N, D], R = D - 1) then Print("OVPROBE mod D - 1") else Print("OVPROBE mod other")
    if (F := Floor(N / D), F = -4) then Print("OVPROBE floor -4") else Print("OVPROBE floor other")
    if (C := Ceil(N / D), C = -3) then Print("OVPROBE ceil -3") else Print("OVPROBE ceil other")
