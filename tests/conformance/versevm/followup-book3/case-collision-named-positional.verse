# Edge of the case-collision rule (#724): Function(X:int) beside
# FUNCTION(?X:int = 420), one positional, one named. OpenVerse tells them
# apart (a named parameter by its name) and prints
#   lower 42 | upper 420
# If Epic refuses it (9200 or 9000), a named parameter does not tell them
# apart.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) admits it (compiled only).
Function(X:int):int = X
FUNCTION(?X:int = 420):int = X

Main():void =
    Print("OVPROBE lower {Function(42)}")
    Print("OVPROBE upper {FUNCTION()}")
