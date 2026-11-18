# Book: Tests/SingleParamArray.versetest:94 (verse_vm_only): functions of
# []int and of tuple(int, int) joined at a declared function type.
F9(:[]int):void = {}
F10(:tuple(int, int)):void = {}
G(P:logic):void =
    F:type{_(:tuple(int, int)):void} = if (P?) { F9 } else { F10 }
    F(1, 2)

Main():void =
    G(true)
    G(false)
    Print("OVPROBE called")
