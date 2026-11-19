# Asks the same of a class cc and an interface CC. OpenVerse refuses it
# (#724). If Epic admits it, it prints
#   lower 1
cc := class:
    V:int = 1

CC := interface:
    Get():int = 2

Main():void =
    Print("OVPROBE lower {cc{}.V}")
