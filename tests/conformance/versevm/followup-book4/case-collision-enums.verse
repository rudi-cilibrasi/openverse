# Asks the same of two enums, ee and EE. OpenVerse refuses it (#724). If
# Epic admits it, it prints
#   compared
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9002 (L7) "Found existing type 'EE' that
# is already being created this compile. Please rename the enumeration to be
# case ".
ee := enum:
    A
    B

EE := enum:
    C
    D

Main():void =
    X:ee = ee.A
    Y:EE = EE.D
    if (X = ee.A, Y = EE.D):
        Print("OVPROBE compared")
