# Book: Tests/Operators/Negate.versetest:14 (verse_vm_only).
Negate(N:int)<computes>:int = -N

Main():void =
    N := Negate(-9223372036854775808)
    if (N > 9223372036854775807):
        Print("OVPROBE above signed 64-bit max")
    else:
        Print("OVPROBE at or below signed 64-bit max")
