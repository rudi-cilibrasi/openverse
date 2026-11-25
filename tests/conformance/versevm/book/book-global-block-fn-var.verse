# Book: Tests/GlobalVariables.versetest:97 (verse_vm_only): link error 9003.
F()<allocates>:int =
    var X:int = 0
    return 1
c0 := class<allocates>{block{F()}}
Submodule := module:
    C0:c0 = c0{}

Main():void =
    Print("OVPROBE linked")
