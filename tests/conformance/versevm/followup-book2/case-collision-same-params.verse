# Book: Tests/Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest:199
# (bp_vm_only), grouped with :187 (methods), :193 and :205 (the return types
# differ): two module functions with the same parameters whose names differ
# only in case. The Book's Blueprint VM refuses them at link time with 9000
# twice (a symbol not found: the name aliasing hides the second function);
# no Verse VM twin. OpenVerse admits them and prints
#   lower 42 | upper 420
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
Function(Value:int):int = Value
FUNCTION(Value:int):int = 420

Main():void =
    Print("OVPROBE lower {Function(42)}")
    Print("OVPROBE upper {FUNCTION(42)}")
