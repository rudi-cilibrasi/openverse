# Follow-up (#724): a one-sided refinement and ints beyond 64 bits. OpenVerse
# prints "natural cast succeeded", "negative cast failed".
natural := type{_X:int where _X >= 0}
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    if (natural[Big * Big]) then Print("OVPROBE natural cast succeeded") else Print("OVPROBE natural cast failed")
    if (natural[-Big * Big]) then Print("OVPROBE negative cast succeeded") else Print("OVPROBE negative cast failed")
