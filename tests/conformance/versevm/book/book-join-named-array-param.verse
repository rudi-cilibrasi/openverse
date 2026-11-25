# Book: Tests/Bugs/SOL-6945-JoinOfTupleOfNamedElementsAndArray.versetest:53
# and :61 (verse_vm_only).
F1(G(:[]int):int):int = G(1, 2, 3)
F2(G(:int, ?X:int):int):int = G(1, ?X := 2)
H1(:any):int = 1
H2(:any):int = 2

Main():void =
    F := if (false?) then F1 else F2
    Print("OVPROBE false branch {F(H1)}")
    G := if (true?) then F1 else F2
    Print("OVPROBE true branch {G(H2)}")
