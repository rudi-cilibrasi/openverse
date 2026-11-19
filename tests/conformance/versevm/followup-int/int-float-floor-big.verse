# Follow-up (#724): Floor of a float beyond 64 bits. The API reference says
# Ceil, Floor, Round and Int raise a halting integer-bounds error outside
# 64 bits; OpenVerse does (the session stops after "before floor"). On the
# Verse VM the result might instead be an int beyond 64 bits ("floor above").
Main():void =
    Print("OVPROBE before floor")
    if (F := Floor[1.0e19]):
        if (F > 9223372036854775807) then Print("OVPROBE floor above") else Print("OVPROBE floor not above")
    else:
        Print("OVPROBE floor failed")
