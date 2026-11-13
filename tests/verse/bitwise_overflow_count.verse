# A left shift of a nonzero int by a count beyond its width is the overflow
# error, after the doublings that stay in range (the Book's bp_vm_only
# BitShiftLeft[5, 0x7FFFFFFFFFFFFFFF]); of zero it is zero.
Main():void =
    if (Z := BitShiftLeft[0, 9223372036854775807]) then Print("zero {Z}")
    if (Y := BitShiftLeft[5, 9223372036854775807]) then Print("unreachable {Y}")
