# Control of join-named-default-fn: a function whose only parameter is named
# and defaulted, as a value of type{_():int}, no join. Book:
# Tests/Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest:36 (valid
# on both VMs, FX() = 2). OpenVerse prints
#   value 2
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints value 2, as OpenVerse does.
F2(?A:int = 2):int = A

Main():void =
    F:type{_():int} = F2
    Print("OVPROBE value {F()}")
