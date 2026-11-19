# Edge of the case-collision rule (#724): a function Function() and a
# constant FUNCTION. OpenVerse admits them and prints
#   lower 42 | upper 420
# If Epic refuses it, a constant and a function collide too.
Function():int = 42
FUNCTION:int = 420

Main():void =
    Print("OVPROBE lower {Function()}")
    Print("OVPROBE upper {FUNCTION}")
