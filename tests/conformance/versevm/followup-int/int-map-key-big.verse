# Follow-up (#724): ints beyond 64 bits as map keys, looked up with equal
# values computed another way. OpenVerse prints "found 2^63", "found 2^126",
# "one entry".
Next(N:int)<computes>:int = N + 1

Main():void =
    Top:int = 9223372036854775807
    Big := Next(Top)
    M:[int]string = map{Big => "a", Big * Big => "b"}
    if (S := M[Top + 1], S = "a") then Print("OVPROBE found 2^63") else Print("OVPROBE missing 2^63")
    if (S := M[(Top + 1) * (Top + 1)], S = "b") then Print("OVPROBE found 2^126") else Print("OVPROBE missing 2^126")
    var N:[int]int = map{}
    if (set N[Big] = 1, set N[Top + 1] = 2, N.Length = 1) then Print("OVPROBE one entry") else Print("OVPROBE not one entry")
