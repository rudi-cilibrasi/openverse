# Edge of the case-collision rule (#724): two functions whose names differ
# only in case, with one parameter type, int, under other names (A, B). Epic
# refuses Function(Value:int) beside FUNCTION(Value:int), 9000
# (followup-book2/case-collision-same-params); does a parameter's name tell
# them apart? OpenVerse compares the types only, and refuses it ("have names
# that differ only in case and take the same parameters"). If Epic admits
# it, it prints
#   lower 42 | upper 420
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9000 (L8) "Local variable `A` not found
# internally in VM.".
Function(A:int):int = A
FUNCTION(B:int):int = 420

Main():void =
    Print("OVPROBE lower {Function(42)}")
    Print("OVPROBE upper {FUNCTION(42)}")
