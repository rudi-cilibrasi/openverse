# Follow-up (#724): Floor of a dividend beyond 64 bits divided by zero. X / Y
# of ints is a rational and fails when Y = 0 (Book ch. 2); Epic's rationals
# and their Floor go past 64 bits (int-rational-big). OpenVerse fails and
# prints "before floor", "floor failed"; a runtime error would stop the
# session after "before floor".
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("OVPROBE before floor")
    if (Floor(Big / 0)) then Print("OVPROBE floor succeeded") else Print("OVPROBE floor failed")
