# Control-like edge: a class cc and a module function CC(). OpenVerse
# measures types against types and functions against functions only, and
# admits it:
#   lower 1 | upper 2
# If Epic refuses it, a type and a function collide too.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) admits it (compiled only).
cc := class:
    V:int = 1

CC():int = 2

Main():void =
    Print("OVPROBE lower {cc{}.V}")
    Print("OVPROBE upper {CC()}")
