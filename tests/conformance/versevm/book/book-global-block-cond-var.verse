# Book: Tests/GlobalVariables.versetest:105 (verse_vm_only): link error 9003,
# the var allocated on the path the initializer takes.
F(Condition:logic)<allocates>:int =
    if (Condition?):
        var X:int = 0
    return 1
c0 := class<allocates>{block{F(true)}}
Submodule := module:
    C0:c0 = c0{}

Main():void =
    Print("OVPROBE linked")
