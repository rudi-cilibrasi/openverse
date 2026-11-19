# Follow-up (#724): an int beyond 64 bits times a float converts it to a
# double. OpenVerse rounds to nearest, ties to even (IEEE's default), and
# prints "tie to even", "above tie up", "odd tie up", as Epic's Verse VM
# does.
Next(N:int)<computes>:int = N + 1

Main():void =
    P := Next(9223372036854775807) * 2
    if ((P + 2048) * 1.0 = 18446744073709551616.0) then Print("OVPROBE tie to even")
    else if ((P + 2048) * 1.0 = 18446744073709555712.0) then Print("OVPROBE tie up")
    else Print("OVPROBE tie other")
    if ((P + 2049) * 1.0 = 18446744073709555712.0) then Print("OVPROBE above tie up")
    else if ((P + 2049) * 1.0 = 18446744073709551616.0) then Print("OVPROBE above tie down")
    else Print("OVPROBE above tie other")
    if ((P + 6144) * 1.0 = 18446744073709559808.0) then Print("OVPROBE odd tie up")
    else if ((P + 6144) * 1.0 = 18446744073709555712.0) then Print("OVPROBE odd tie down")
    else Print("OVPROBE odd tie other")
