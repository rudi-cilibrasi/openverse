# Book: Tests/FunctionTypes.versetest:220 (verse_vm_only, assert_valid): the
# join of ()->int and ()->float is callable.
f28():int = return 1
f29():float = return 1.0
f30(b:logic):void =
    g := if (b?) {f28} else {f29}
    g()

Main():void =
    f30(true)
    f30(false)
    Print("OVPROBE called")
