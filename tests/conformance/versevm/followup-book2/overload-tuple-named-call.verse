# Book: Tests/Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest:62
# (untagged): F(X:tuple(float, float), ?E:float = 0.1) called as F(1.0,
# 2.0). The Book refuses it on both VMs, 3509 ("Doesn't work in ShipVerse,
# but generate a somewhat ok error message"). OpenVerse admits it, packs the
# two arguments into the tuple and prints
#   packed into the tuple
# If UEFN 43.12 refuses it, OpenVerse should not pack positional arguments
# into a tuple parameter that has a named parameter beside it. Control:
# overload-tuple-named-call-control (the tuple written out, the Book's :55).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3509 (L12) "This function parameter
# expects a value of type tuple(tuple(float,float),?E:float = ...), but this
# argument is an incompatible value of type tuple(type{1.000000".
F(X:tuple(float, float), ?E:float = 0.1):float = X(0) + X(1) + E

Main():void =
    Sum := F(1.0, 2.0)
    if (Sum > 3.0, Sum < 3.2):
        Print("OVPROBE packed into the tuple")
