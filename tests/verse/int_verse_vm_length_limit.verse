# An int has at most 2^20 bits, the Verse VM's MaxLengthBits: a longer
# result is the overflow error, not a failure (#724; the Book of Verse's
# Math/Bitwise.versetest:222-225, verse_vm_only: BitShiftLeft[1, 1048575] is
# an int, BitShiftLeft[1, 1048576] the runtime error). Squaring 2^(2^19)
# reaches it by multiplication.
Main():void =
    var X:int = 2
    for (I := 1..19):
        set X *= X
    Print("2^(2^19) computed")
    Y := (X - 1) * (X + 1)
    Print("2^(2^20) - 1 computed")
    if (Y + 1 > Y) then Print("unreachable")
    Print("not reached")
