# Control-like edge: a class cc in module mm and a class CC at the top
# level, two scopes. OpenVerse admits it:
#   lower 1 | upper 2
# If Epic refuses it, types collide across modules.
mm := module:
    cc<public> := class:
        V<public>:int = 1

CC := class:
    V:int = 2

Main():void =
    Print("OVPROBE lower {mm.cc{}.V}")
    Print("OVPROBE upper {CC{}.V}")
