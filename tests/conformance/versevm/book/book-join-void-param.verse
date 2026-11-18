# Book: Tests/Void.versetest:140 and :144 (verse_vm_only): the join of a
# function taking void and one taking int is callable with an int.
VoidInput(:void):int = 19
IntIdentity(X:int):int = X

Main():void =
    F := if (false?) { VoidInput } else { IntIdentity }
    Print("OVPROBE false branch {F(1)}")
    G := if (true?) { VoidInput } else { IntIdentity }
    Print("OVPROBE true branch {G(2)}")
