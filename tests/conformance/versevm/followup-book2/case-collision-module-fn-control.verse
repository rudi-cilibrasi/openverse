# Control of case-collision-module-fn. Book:
# Tests/Bugs/FORT-793952-CaseInsensitiveNameCollisions.versetest:106, valid
# on both VMs: names that differ only in case, told apart by their
# parameters. OpenVerse prints
#   lower 42 | upper 420
# A refusal here means the names themselves are refused, whatever their
# parameters.
Function(Value:int):int = Value
FUNCTION():int = 420

Main():void =
    Print("OVPROBE lower {Function(42)}")
    Print("OVPROBE upper {FUNCTION()}")
