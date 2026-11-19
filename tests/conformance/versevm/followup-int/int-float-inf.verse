# Follow-up (#724): an int past the largest double (2^1071) times a float.
# OpenVerse gives Inf (round to nearest) and prints "big computed",
# "infinity", as Epic's Verse VM does.
Next(N:int)<computes>:int = N + 1

Main():void =
    var X:int = Next(9223372036854775807)
    for (I := 1..4):
        set X *= X
    set X *= Next(9223372036854775807)
    Print("OVPROBE big computed")
    if (X * 1.0 = Inf) then Print("OVPROBE infinity") else Print("OVPROBE finite")
