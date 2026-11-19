# Asks the same of a class cc and a struct CC. OpenVerse refuses it (#724).
# If Epic admits it, it prints
#   lower 1 | upper 2
cc := class:
    V:int = 1

CC := struct:
    V:int = 2

Main():void =
    Print("OVPROBE lower {cc{}.V}")
    Print("OVPROBE upper {CC{}.V}")
