# An omitted computed default runs at its field's place: here after the
# choice, which is written first and so runs at X's place (#724: the fields
# given are evaluated in the order written), once for each of its values.
G()<transacts>:int =
    Print("g")
    7
pt := struct { X : int; Y : int = G(); Z : int }
Main()<transacts>:void =
    for (P := pt{Z := 1 | 2, X := 0}):
        Print("{P.X} {P.Y} {P.Z}")
