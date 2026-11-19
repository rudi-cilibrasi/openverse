# Edge of the 3509 rule (#724): F(1.0, 2.0, ?E := 3.0) of F(X:tuple(float,
# float), ?E:float = 0.1), the named argument given. OpenVerse packs nothing
# beside a named parameter and refuses it ("F takes 1 positional
# argument(s), found 2: several arguments are not packed ..."). If Epic
# admits it, it prints
#   packed into the tuple
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3509 (L9) "This function parameter
# expects a value of type tuple(tuple(float,float),?E:float = ...), but this
# argument is an incomp".
F(X:tuple(float, float), ?E:float = 0.1):float = X(0) + X(1) + E

Main():void =
    Sum := F(1.0, 2.0, ?E := 3.0)
    if (Sum > 5.9, Sum < 6.1):
        Print("OVPROBE packed into the tuple")
