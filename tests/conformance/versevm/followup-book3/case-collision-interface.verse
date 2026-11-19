# Edge of the case-collision rule (#724): an interface's two methods with
# defaults, Function() and FUNCTION(), and a class that inherits both.
# OpenVerse does not measure an interface's methods, and prints
#   lower 42 | upper 420
# If Epic refuses it, an interface's methods collide as a class's do.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 9200 (L7) "Found multiple functions that
# map to the same target function. Please rename the function to be case
# insensitive unique.".
ii := interface:
    Function():int = 42
    FUNCTION():int = 420

impl := class(ii) {}

Main():void =
    Obj := impl{}
    Print("OVPROBE lower {Obj.Function()}")
    Print("OVPROBE upper {Obj.FUNCTION()}")
