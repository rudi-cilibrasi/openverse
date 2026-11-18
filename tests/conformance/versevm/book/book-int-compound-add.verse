# Book: Tests/Operators/BinaryAddInt.versetest:65 (verse_vm_only).
Largest()<computes>:int = 9223372036854775807

Main():void =
    var X:int = Largest()
    Print("OVPROBE start")
    set X += 1
    if (X > 9223372036854775807):
        Print("OVPROBE above signed 64-bit max")
    else:
        Print("OVPROBE at or below signed 64-bit max")
