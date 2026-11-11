# A computed default before a field choice in a comparison is lifted once.
G()<transacts>:int =
    Print("g")
    7
dd := struct { X : int; Y : int = G(); Z : int }
Main()<transacts>:void =
    if (0 < dd{Z := 1 | 2, X := 0}.Z):
        Print("lt")
