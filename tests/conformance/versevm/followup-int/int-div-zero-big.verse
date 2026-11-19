# Follow-up (#724): a zero divisor with a dividend beyond 64 bits. Ints in
# 64 bits fail (Book ch. 2); OpenVerse fails for these too and prints the
# three "failed" lines. A runtime error instead would stop the session.
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    if (Quotient[Big, 0]) then Print("OVPROBE quotient succeeded") else Print("OVPROBE quotient failed")
    if (Mod[Big, 0]) then Print("OVPROBE mod succeeded") else Print("OVPROBE mod failed")
    if (Floor(Big / 0)) then Print("OVPROBE floor succeeded") else Print("OVPROBE floor failed")
