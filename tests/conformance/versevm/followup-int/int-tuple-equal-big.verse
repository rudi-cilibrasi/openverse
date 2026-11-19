# Follow-up (#724): equality of tuples holding ints beyond 64 bits (not
# reached in int-intrinsics-big). OpenVerse compares them exactly and prints
# "before tuples", "tuples equal", "tuples differ"; a runtime error would
# stop the session after "before tuples".
Next(N:int)<computes>:int = N + 1

Main():void =
    Top:int = 9223372036854775807
    Big := Next(Top)
    Print("OVPROBE before tuples")
    if ((Big, 2) = (Top + 1, 2)) then Print("OVPROBE tuples equal") else Print("OVPROBE tuples not equal")
    if ((Big, 2) <> (Top, 2)) then Print("OVPROBE tuples differ") else Print("OVPROBE tuples not different")
