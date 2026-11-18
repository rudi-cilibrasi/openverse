# Book: Tests/Math/Bitwise.versetest:204 and :208 (verse_vm_only).
Shifted(N:int, By:int)<computes><decides>:int = BitShiftLeft[N, By]

Main():void =
    if (A := Shifted[1, 63]):
        if (A > 9223372036854775807):
            Print("OVPROBE shift 63 above signed 64-bit max")
        else:
            Print("OVPROBE shift 63 at or below signed 64-bit max")
    else:
        Print("OVPROBE shift 63 failed")
    if (B := Shifted[1, 200], BitShiftRight[B, 200] = 1):
        Print("OVPROBE shift 200 round trip")
    else:
        Print("OVPROBE shift 200 failed")
