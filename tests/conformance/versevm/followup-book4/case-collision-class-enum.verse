# Asks the same of a class cc and an enum CC. OpenVerse refuses it (#724).
# If Epic admits it, it prints
#   lower 1
cc := class:
    V:int = 1

CC := enum:
    A
    B

Main():void =
    X:CC = CC.A
    if (X = CC.A):
        Print("OVPROBE lower {cc{}.V}")
