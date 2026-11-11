# An omitted computed default runs before the later field choice.
G()<transacts>:int =
    Print("g")
    7
pt := struct { X : int; Y : int = G(); Z : int }
Main()<transacts>:void =
    for (P := pt{Z := 1 | 2, X := 0}):
        Print("{P.X} {P.Y} {P.Z}")
