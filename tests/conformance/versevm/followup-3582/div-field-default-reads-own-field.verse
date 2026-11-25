# 3582 follow-up (#724), compile only: a field default that reads another
# field of the same object. The Book's tests refuse it with 3502
# (Features/DefaultValueAssignment.versetest:65-67), not 3582: this probe
# asks which UEFN 43.12 reports. OpenVerse refuses it: "unknown identifier
# 'A'".
thing := class:
    A:int = 1
    B:int = A + 1

Main():void =
    T := thing{}
    Print("OVPROBE b {T.B}")
