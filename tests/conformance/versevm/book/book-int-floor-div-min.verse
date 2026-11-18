# Book: Tests/Operators/BinaryDivInt.versetest:49 (verse_vm_only).
FloorQuotient(A:int, B:int)<computes><decides>:int = Floor(A / B)

Main():void =
    if (N := FloorQuotient[-9223372036854775808, -1]):
        if (N > 9223372036854775807):
            Print("OVPROBE above signed 64-bit max")
        else:
            Print("OVPROBE at or below signed 64-bit max")
    else:
        Print("OVPROBE division failed")
