# A where-constrained int type's cast compares the bounds exactly (#724):
# 2^63 fails a 64-bit refinement, as on Epic's Verse VM (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, 2026-11-18: the probe
# book-int-where-i64 prints "big computed", "i64 cast failed";
# WhereConstrainedInts.versetest:224-227, verse_vm_only).
i64 := type{_X:int where _X >= -9223372036854775808, _X <= 9223372036854775807}
natural := type{_X:int where _X >= 0}
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("big computed")
    if (i64[Big]) then Print("i64 cast succeeded") else Print("i64 cast failed")
    if (i64[Big - 1]) then Print("i64 cast of the maximum succeeded")
    if (not i64[-Big - 1]) then Print("i64 cast below the minimum failed")
    if (i64[-Big]) then Print("i64 cast of the minimum succeeded")
    if (N := natural[Big * Big]) then Print("natural cast succeeded")
    if (not natural[-Big * Big]) then Print("natural cast of a negative failed")
