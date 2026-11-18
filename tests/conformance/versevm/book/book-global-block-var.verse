# Book: Tests/GlobalVariables.versetest:86 (verse_vm_only): link error 9003,
# a module constant whose construction runs a block that allocates a var.
c0 := class<allocates>{block{var X:int = 0}}
C0:c0 = c0{}

Main():void =
    Print("OVPROBE linked")
