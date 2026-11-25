# Asks the same of two interfaces, ii and II. OpenVerse refuses it (#724).
# If Epic admits it, it prints
#   defined
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9002 (L6) "Found existing type 'II' that
# is already being created this compile. Please rename the interface to be
# case in".
ii := interface:
    Get():int = 1

II := interface:
    Get():int = 2

Main():void =
    Print("OVPROBE defined")
