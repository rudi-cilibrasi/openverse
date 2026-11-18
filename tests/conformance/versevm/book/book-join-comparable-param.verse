# Book: Tests/Comparable.versetest:216 (verse_vm_only, assert_valid; the BPVM
# twin is IR error 3502, "not yet implemented").
comparable_class := class<unique>{}
F(H(:comparable_class):void):void = {}
G(H1(:comparable_class):void, H2(:comparable):void):void = F(if (true?) {H1} else {H2})

Main():void =
    Print("OVPROBE compiled")
