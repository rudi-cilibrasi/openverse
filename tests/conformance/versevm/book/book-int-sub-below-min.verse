# Book: Tests/Operators/BinarySubInt.versetest:41 (verse_vm_only).
Less(N:int)<computes>:int = N - 1

Main():void =
    N := Less(-9223372036854775808)
    if (N < -9223372036854775808):
        Print("OVPROBE below signed 64-bit min")
    else:
        Print("OVPROBE at or above signed 64-bit min")
