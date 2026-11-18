# Book: Tests/GlobalVariables.versetest:90 (verse_vm_only): link error 9003.
F()<allocates>:c1 = c1{}
c0 := class<allocates>{block{F()}}
c1 := class<allocates>{var X:int = 0}
Submodule := module:
    C0:c0 = c0{}

Main():void =
    Print("OVPROBE linked")
