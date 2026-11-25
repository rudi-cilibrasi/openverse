# Control of overload-tuple-named-call: the tuple written out, F((1.0, 2.0),
# ?E := 10.0). Book:
# Tests/Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest:55 (valid
# on both VMs, = 13.0). OpenVerse prints
#   explicit tuple
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints explicit tuple, as
# OpenVerse does.
F(X:tuple(float, float), ?E:float = 0.1):float = X(0) + X(1) + E

Main():void =
    Sum := F((1.0, 2.0), ?E := 10.0)
    if (Sum > 12.9, Sum < 13.1):
        Print("OVPROBE explicit tuple")
