# Follow-up (#724): Min, Max, Clamp and Sgn of ints beyond 64 bits, and
# equality inside arrays and tuples. OpenVerse prints "min max", "clamp",
# "sgn", "containers equal".
Next(N:int)<computes>:int = N + 1

Main():void =
    Top:int = 9223372036854775807
    Big := Next(Top)
    if (Min(Big, Top) = Top, Max(-Big - 1, -Top) = -Top) then Print("OVPROBE min max")
    if (Clamp(Big, 0, 10) = 10, Clamp(-Big * 2, -5, 5) = -5) then Print("OVPROBE clamp")
    if (Sgn(Big) = 1, Sgn(-Big * Big) = -1) then Print("OVPROBE sgn")
    if (array{Big, 1} = array{Top + 1, 1}, (Big, 2) = (Top + 1, 2), array{Big} <> array{Top}) then Print("OVPROBE containers equal")
