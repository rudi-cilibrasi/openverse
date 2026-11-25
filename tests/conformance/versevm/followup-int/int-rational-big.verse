# Follow-up (#724): rationals of ints beyond 64 bits and their Floor and
# Ceil. OpenVerse prints "floor 2^63", "ceil 2^63 + 1", "reduced".
Next(N:int)<computes>:int = N + 1

Main():void =
    Top:int = 9223372036854775807
    Big := Next(Top)
    if (R := (Big * Big + 1) / Big):
        if (Floor(R) = Top + 1) then Print("OVPROBE floor 2^63") else Print("OVPROBE floor other")
        if (Ceil(R) = Top + 2) then Print("OVPROBE ceil 2^63 + 1") else Print("OVPROBE ceil other")
    if (R := (Big * 6) / (Big * 4), R = 3 / 2) then Print("OVPROBE reduced") else Print("OVPROBE not reduced")
