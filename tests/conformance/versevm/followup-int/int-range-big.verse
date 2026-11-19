# Follow-up (#724): a range across the top of the 64-bit range. OpenVerse
# iterates 2^63 - 2 .. 2^63 + 1 one by one: "count 4", "two above".
Next(N:int)<computes>:int = N + 1

Main():void =
    Top:int = 9223372036854775807
    Hi := Next(Top) + 1
    var Count:int = 0
    var Above:int = 0
    for (I := Top - 1..Hi):
        set Count += 1
        if (I > Top) then set Above += 1
    if (Count = 4) then Print("OVPROBE count 4") else Print("OVPROBE count not 4")
    if (Above = 2) then Print("OVPROBE two above") else Print("OVPROBE not two above")
