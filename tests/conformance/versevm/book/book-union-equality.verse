# Book: Tests/Union.versetest:221 (verse_vm_only; no chapter describes union).
u1 := union:
    N:int
    S:string
    V:void

Main():void =
    if (u1.N(1) = u1.N(1)):
        Print("OVPROBE equal")
    else:
        Print("OVPROBE not equal")
