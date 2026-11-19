# Follow-up (#724): the longest int. The Book's verse_vm_only tests pin
# MaxLengthBits = 2^20 for shifts (Math/Bitwise.versetest:222-225).
# OpenVerse computes 2^(2^20) - 1 by multiplication and prints "longest
# computed", "longer than half". Epic's Verse VM printed nothing in three
# sessions and reported no error; the cause is not known yet.
Main():void =
    var H:int = 2
    for (I := 1..19):
        set H *= H
    M := (H - 1) * (H + 1)
    Print("OVPROBE longest computed")
    if (M > H) then Print("OVPROBE longer than half")
