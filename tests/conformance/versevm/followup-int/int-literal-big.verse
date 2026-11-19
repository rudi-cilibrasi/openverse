# Follow-up (#724): an int literal beyond 64 bits. The Book (ch. 2) says
# literals must fit in 64 bits; OpenVerse refuses this ("integer literal
# 9223372036854775808 does not fit in 64 bits"), as Epic does (3555).
Main():void =
    X:int = 9223372036854775808
    if (X > 9223372036854775807) then Print("OVPROBE above")
