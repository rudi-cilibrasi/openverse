# Book: Tests/Void.versetest:148 and :152 (verse_vm_only): the join of a
# function returning void and one returning int is callable.
VoidOutput(:int):void = {}
IntIdentity(X:int):int = X

Main():void =
    F := if (false?) { VoidOutput } else { IntIdentity }
    F(0)
    Print("OVPROBE false branch called")
    G := if (true?) { VoidOutput } else { IntIdentity }
    G(0)
    Print("OVPROBE true branch called")
