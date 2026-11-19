# Asks the same of a class cc and an enum CC. OpenVerse refuses it (#724).
# If Epic admits it, it prints
#   lower 1
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9002 (L6) "Found existing type 'CC' that
# is already being created this compile. Please rename the enumeration to be
# case ".
cc := class:
    V:int = 1

CC := enum:
    A
    B

Main():void =
    X:CC = CC.A
    if (X = CC.A):
        Print("OVPROBE lower {cc{}.V}")
