# expect: 4:11: field 'X' of pt is given twice
pt := struct { X : int }
Main()<transacts>:void =
    P := pt{X := 1, X := 2}
    Print("{P.X}")
