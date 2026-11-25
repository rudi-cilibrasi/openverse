# Book: Tests/WhereConstrainedInts.versetest:219 (verse_vm_only).
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("OVPROBE big computed")
    if (int[Big]):
        Print("OVPROBE int cast succeeded")
    else:
        Print("OVPROBE int cast failed")
