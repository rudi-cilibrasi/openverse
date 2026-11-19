# Book: Tests/Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest:62
# (untagged): F(X:tuple(float, float), ?E:float = 0.1) called as F(1.0,
# 2.0). The Book refuses it on both VMs, 3509 ("Doesn't work in ShipVerse,
# but generate a somewhat ok error message"). OpenVerse admits it, packs the
# two arguments into the tuple and prints
#   packed into the tuple
# If UEFN 43.12 refuses it, OpenVerse should not pack positional arguments
# into a tuple parameter that has a named parameter beside it. Control:
# overload-tuple-named-call-control (the tuple written out, the Book's :55).
F(X:tuple(float, float), ?E:float = 0.1):float = X(0) + X(1) + E

Main():void =
    Sum := F(1.0, 2.0)
    if (Sum > 3.0, Sum < 3.2):
        Print("OVPROBE packed into the tuple")
