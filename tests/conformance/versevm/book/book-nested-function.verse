# Book: Tests/NestedFunctions.versetest:41 (verse_vm_only; nested functions,
# docs/06_functions.md, an unreleased feature).
HelloWorld := module:
    F<public>(X:int):int =
        G():int = X
        G()

Main():void =
    Print("OVPROBE nested {HelloWorld.F(1)} {HelloWorld.F(2)}")
