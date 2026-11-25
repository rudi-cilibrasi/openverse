# A tuple parameter beside a named one takes the tuple written out (#724):
# UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086) admits and runs
# followup-book2/overload-tuple-named-call-control ("explicit tuple"; the
# Book's FORT-744399:55). Without a named parameter, two arguments still
# pack into the single tuple parameter.
F(X:tuple(float, float), ?E:float = 0.1):float = X(0) + X(1) + E
G(X:tuple(int, int)):int = X(0) + X(1)
Main():void =
    Sum := F((1.0, 2.0), ?E := 10.0)
    if (Sum > 12.9, Sum < 13.1):
        Print("explicit tuple")
    Plain := F((1.0, 2.0))
    if (Plain > 3.0, Plain < 3.2):
        Print("default named")
    Print("packed {G(3, 4)}")
