# A left shift past 64 bits is an int (#724; the Book's Math/Bitwise.versetest,
# verse_vm_only: BitShiftLeft[1, 63] = 2^63), whose ToString is the overflow
# error, not a failure: the program ends with exit 2.
Main():void =
    if (X := BitShiftLeft[-1, 63]) then Print("in range {X}")
    if (Y := BitShiftLeft[1, 63]) then Print("unreachable {Y}") else Print("unreachable: no failure")
    Print("unreachable")
