# Book: Tests/Operators/BinaryMulInt.versetest:49 (verse_vm_only).
Times(A:int, B:int)<computes>:int = A * B

Main():void =
    N := Times(-9223372036854775808, -1)
    if (N > 9223372036854775807):
        Print("OVPROBE above signed 64-bit max")
    else:
        Print("OVPROBE at or below signed 64-bit max")
