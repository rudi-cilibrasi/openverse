# A left shift whose result is out of the 64-bit range is the overflow error
# (the Book's Math/Bitwise.versetest, bp_vm_only: BitShiftLeft[1, 63]), not a
# failure: the program ends with exit 2.
Main():void =
    if (X := BitShiftLeft[-1, 63]) then Print("in range {X}")
    if (Y := BitShiftLeft[1, 63]) then Print("unreachable {Y}") else Print("unreachable: no failure")
    Print("unreachable")
