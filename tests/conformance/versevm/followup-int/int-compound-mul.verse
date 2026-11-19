# Follow-up (#724): set *= and set -= past 64 bits. OpenVerse prints
# "squared", "minus one".
Next(N:int)<computes>:int = N + 1

Main():void =
    Top:int = 9223372036854775807
    var X:int = Next(Top)
    set X *= X
    if (X = (Top + 1) * (Top + 1)) then Print("OVPROBE squared") else Print("OVPROBE not squared")
    set X -= X + 1
    if (X = -1) then Print("OVPROBE minus one") else Print("OVPROBE not minus one")
