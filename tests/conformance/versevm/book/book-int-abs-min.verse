# Book: Tests/Intrinsics/Abs.versetest:17 (verse_vm_only).
Magnitude(N:int)<computes>:int = Abs(N)

Main():void =
    N := Magnitude(-9223372036854775808)
    if (N > 9223372036854775807):
        Print("OVPROBE above signed 64-bit max")
    else:
        Print("OVPROBE at or below signed 64-bit max")
