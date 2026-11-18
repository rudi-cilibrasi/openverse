# Book: Tests/WhereConstrainedInts.versetest:224 (verse_vm_only).
i64 := type{_X:int where _X >= -9223372036854775808, _X <= 9223372036854775807}

Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("OVPROBE big computed")
    if (i64[Big]):
        Print("OVPROBE i64 cast succeeded")
    else:
        Print("OVPROBE i64 cast failed")
