# Asks the same of two enums, ee and EE. OpenVerse refuses it (#724). If
# Epic admits it, it prints
#   compared
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
