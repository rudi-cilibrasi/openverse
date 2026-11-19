# Control-like edge: a class cc and a module function CC(). OpenVerse
# measures types against types and functions against functions only, and
# admits it:
#   lower 1 | upper 2
# If Epic refuses it, a type and a function collide too.
cc := class:
    V:int = 1

CC():int = 2

Main():void =
    Print("OVPROBE lower {cc{}.V}")
    Print("OVPROBE upper {CC()}")
