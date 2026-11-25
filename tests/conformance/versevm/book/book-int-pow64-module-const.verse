# Book: Tests/Math/Bitwise.versetest:73 (verse_vm_only): a module constant
# beyond 64 bits, then BitOr on it.
TwoTo64:int = (9223372036854775807 + 1) * 2

Main():void =
    Print("OVPROBE main entered")
    if (BitOr(TwoTo64, 1) = TwoTo64 + 1):
        Print("OVPROBE or added one")
    else:
        Print("OVPROBE or different")
