# Book: Tests/GlobalVariables.versetest:143 (valid on both VMs): the var is
# on a path the initializer does not take.
F(Condition:logic)<allocates>:int =
    if (Condition?):
        var X:int = 0
    return 1
c0 := class<allocates>{block{F(false)}}
Submodule := module:
    C0:c0 = c0{}

Main():void =
    Print("OVPROBE linked")
