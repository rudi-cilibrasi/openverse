# The bitwise functions on ints beyond 64 bits (#724): the Book of Verse's
# verse_vm_only cases (Math/Bitwise.versetest:62-100, 213-219, 222-233,
# 238-247, 252-258); Epic's Verse VM (UEFN 43.12,
# ++Fortnite+Release-43.12-CL-60598086, 2026-11-18) prints the first four
# lines (the probe book-int-bitwise-pow63). UEFN 43.12 has no BitShiftLeft
# or BitShiftRight (error 3506), so the shift lines follow the Book alone.
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("big computed")
    if (BitAnd(Big, 1) = 0) then Print("and zero")
    if (BitOr(Big, 0) = Big) then Print("or unchanged")
    if (BitNot(Big) = -(Big + 1)) then Print("not negated")
    P := Big * 2
    if (BitOr(P, 1) = P + 1, BitAnd(P, P) = P, BitAnd(-P, -P) = -P, BitAnd(P, -P) = P,
        BitAnd(-P, -1) = -P, BitAnd(-P, 7) = 0) then Print("and, or: 2^64")
    if (BitOr(P, -P) = -P, BitOr(-P, -1) = -1, BitOr(-P, 7) = -P + 7) then Print("or: mixed signs")
    if (BitXor(P, P) = 0, BitXor(-P, -P) = 0, BitXor(P, -P) = -(P * 2)) then Print("xor: mixed signs")
    if (BitNot(P) = -(P + 1), BitNot(-P) = P - 1, BitNot(BitNot(-P)) = -P) then Print("not: mixed signs")
    if (BitShiftLeft[1, 63] = Big, BitShiftLeft[1, 64] = P, BitShiftLeft[-2, 63] = -P,
        BitShiftRight[BitShiftLeft[1, 200], 200] = 1) then Print("shifts past 64 bits")
    if (BitShiftLeft[P, 64] = P * P, BitShiftLeft[-P, 3] = -P * 8, BitShiftRight[P, 64] = 1,
        BitShiftRight[-P, 64] = -1, BitShiftRight[-P - 1, 64] = -2,
        BitShiftRight[1 - P * P, 1] = -BitShiftLeft[1, 127]) then Print("multi-word shifts")
    if (BitShiftLeft[0, P] = 0, BitShiftRight[12345, P] = 0, BitShiftRight[-12345, P] = -1,
        BitShiftRight[P, P] = 0, not BitShiftLeft[0, -P], not BitShiftRight[1, -P],
        not BitShiftRight[P, -2]) then Print("counts past 64 bits")
    # the Verse VM's longest int: a magnitude of 2^20 bits (and one bit more,
    # int_verse_vm_length_limit)
    if (L := BitShiftLeft[-1, 1048575], BitShiftRight[L, 1048575] = -1, BitShiftRight[L, 1] = L / 2)
    then Print("2^20 bits")
