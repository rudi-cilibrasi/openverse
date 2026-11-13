# The bitwise functions (Book of Verse ch. 4, "Bitwise Operations" and "Bit
# Shift Operations", and its API reference): two's complement sign-extended
# without limit, on openverse's 64-bit ints (the Blueprint VM's: a result out
# of range is the overflow error, bitwise_overflow_*). BitNot(X) is -X - 1;
# the shifts fail on a negative count, and a right shift rounds toward minus
# infinity, 0 or -1 once every bit is shifted out.
Top:int = 9223372036854775807
Bottom:int = -9223372036854775807 - 1
log := class:
    var Text:string = ""
Note(L:log, X:int)<transacts>:int =
    set L.Text += "<{X}>"
    X
Main():void =
    Print("and {BitAnd(12, 10)} {BitAnd(-1, 777)} {BitAnd(-4, 6)} {BitAnd(-6, -7)} {BitAnd(Top, Bottom)} {BitAnd(Bottom, Bottom)}")
    Print("or {BitOr(12, 10)} {BitOr(-1, 0)} {BitOr(Top, Bottom)} {BitOr(Bottom, 1)} {BitOr(-8, 3)} {BitOr(5, -16)}")
    Print("xor {BitXor(12, 10)} {BitXor(99, 99)} {BitXor(Top, -1)} {BitXor(Top, Bottom)} {BitXor(-5, 3)}")
    Print("not {BitNot(0)} {BitNot(-1)} {BitNot(41)} {BitNot(Top)} {BitNot(Bottom)} {BitNot(BitNot(-77))}")
    if (BitNot(BitAnd(13, 7)) = BitOr(BitNot(13), BitNot(7))) then Print("De Morgan")
    Print("xor twice {BitXor(BitXor(1000, 77), 77)}")
    if (A := BitShiftLeft[3, 5], B := BitShiftLeft[-5, 2], C := BitShiftLeft[1, 62], D := BitShiftLeft[-1, 63]):
        Print("left {A} {B} {C} {D}")
    if (A := BitShiftLeft[0, 63], B := BitShiftLeft[0, Top], C := BitShiftLeft[7, 0]):
        Print("left zero {A} {B} {C}")
    if (A := BitShiftRight[96, 5], B := BitShiftRight[-96, 5], C := BitShiftRight[-97, 5], D := BitShiftRight[Bottom, 63]):
        Print("right {A} {B} {C} {D}")
    if (A := BitShiftRight[12345, 64], B := BitShiftRight[-12345, 1000], C := BitShiftRight[5, Top], D := BitShiftRight[Top, 62]):
        Print("right out {A} {B} {C} {D}")
    if (BitShiftLeft[5, -1]) then Print("wrong") else Print("left -1 fails")
    if (BitShiftRight[5, Bottom]) then Print("wrong") else Print("right min fails")
    Print("or else {BitShiftLeft[5, -2] or 7} {BitShiftRight[BitShiftLeft[-12345, 8] or 0, 8] or 0}")
    # (each argument once, in order)
    L := log{}
    Print("order {BitAnd(Note(L, 6), Note(L, 3))} {L.Text}")
