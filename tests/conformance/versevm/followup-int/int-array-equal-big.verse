# Follow-up (#724): equality of arrays holding ints beyond 64 bits (not
# reached in int-intrinsics-big). OpenVerse compares them exactly and prints
# "before arrays", "arrays equal", "arrays differ"; a runtime error would
# stop the session after "before arrays".
Next(N:int)<computes>:int = N + 1

Main():void =
    Top:int = 9223372036854775807
    Big := Next(Top)
    Print("OVPROBE before arrays")
    if (array{Big, 1} = array{Top + 1, 1}) then Print("OVPROBE arrays equal") else Print("OVPROBE arrays not equal")
    if (array{Big} <> array{Top}) then Print("OVPROBE arrays differ") else Print("OVPROBE arrays not different")
