# A left shift of a nonzero int by a count of 2^20 or more is the overflow
# error: no int is that long (#724; the Book's verse_vm_only
# BitShiftLeft[5, 0x7FFFFFFFFFFFFFFF], "MaxLengthBits"); of zero it is zero.
Main():void =
    if (Z := BitShiftLeft[0, 9223372036854775807]) then Print("zero {Z}")
    if (Y := BitShiftLeft[5, 9223372036854775807]) then Print("unreachable {Y}")
