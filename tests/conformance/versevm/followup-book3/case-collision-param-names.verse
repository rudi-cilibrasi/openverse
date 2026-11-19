# Edge of the case-collision rule (#724): two functions whose names differ
# only in case, with one parameter type, int, under other names (A, B). Epic
# refuses Function(Value:int) beside FUNCTION(Value:int), 9000
# (followup-book2/case-collision-same-params); does a parameter's name tell
# them apart? OpenVerse compares the types only, and refuses it ("have names
# that differ only in case and take the same parameters"). If Epic admits
# it, it prints
#   lower 42 | upper 420
Function(A:int):int = A
FUNCTION(B:int):int = 420

Main():void =
    Print("OVPROBE lower {Function(42)}")
    Print("OVPROBE upper {FUNCTION(42)}")
