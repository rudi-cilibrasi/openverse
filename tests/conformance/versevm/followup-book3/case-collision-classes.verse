# Edge of the case-collision rule (#724): two classes, cc and CC. The rule
# OpenVerse takes is the functions'; it admits two classes and prints
#   lower 1 | upper 2
# If Epic refuses it (9002, an existing type?), classes collide too.
cc := class:
    V:int = 1

CC := class:
    V:int = 2

Main():void =
    Print("OVPROBE lower {cc{}.V}")
    Print("OVPROBE upper {CC{}.V}")
