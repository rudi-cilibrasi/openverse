# int[X] succeeds for every int, past 64 bits too (#724): Epic's Verse VM
# (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use Verse VM",
# 2026-11-18) prints "big computed", "int cast succeeded" for the probe
# book-int-cast-int; the Book of Verse's tests,
# WhereConstrainedInts.versetest:219-222 (verse_vm_only), cast 2^63 and
# -2^63 - 1 too. A 64-bit refinement's cast of them fails
# (int_verse_vm_where).
i64 := type{_X:int where _X >= -9223372036854775808, _X <= 9223372036854775807}
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("big computed")
    if (int[Big]) then Print("int cast succeeded") else Print("int cast failed")
    if (int[9223372036854775807], int[-9223372036854775808]) then Print("64-bit ends")
    if (Below := int[-9223372036854775808 - 1], Below < -Big + 1) then Print("below the 64-bit range")
    if (X := int[Big * Big], X = Big * Big, not i64[X]) then Print("2^126 is an int, not an i64")
