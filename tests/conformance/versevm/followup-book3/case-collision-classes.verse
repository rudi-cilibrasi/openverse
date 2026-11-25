# Edge of the case-collision rule (#724): two classes, cc and CC. The rule
# OpenVerse takes is the functions'; it admits two classes and prints
#   lower 1 | upper 2
# If Epic refuses it (9002, an existing type?), classes collide too.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9002 (L7) "Found existing type 'CC' that
# is already being created this compile. Please rename the class to be case
# insensitive uniq".
cc := class:
    V:int = 1

CC := class:
    V:int = 2

Main():void =
    Print("OVPROBE lower {cc{}.V}")
    Print("OVPROBE upper {CC{}.V}")
