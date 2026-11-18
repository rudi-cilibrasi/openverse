# Book: Tests/Math/Bitwise.versetest:62, :64 and :66 (verse_vm_only).
Next(N:int)<computes>:int = N + 1

Main():void =
    Big := Next(9223372036854775807)
    Print("OVPROBE big computed")
    if (BitAnd(Big, 1) = 0):
        Print("OVPROBE and zero")
    else:
        Print("OVPROBE and nonzero")
    if (BitOr(Big, 0) = Big):
        Print("OVPROBE or unchanged")
    else:
        Print("OVPROBE or changed")
    if (BitNot(Big) = -(Big + 1)):
        Print("OVPROBE not negated")
    else:
        Print("OVPROBE not different")
