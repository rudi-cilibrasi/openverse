# char32 (the spec grammar's Char32): 0u literals, Unicode scalar values;
# ints in Verse Core, printed as UTF-8 (1 to 4 bytes).

Next(C:char32):char32 = if (C = 0u41) then 0u42 else C
Main():void =
    A := 0u41
    E := 0uE9
    Euro := 0u20AC
    Smile := 0u1F600
    Last := 0u10FFFF
    Print("{A}{E}{Euro}{Smile}")
    S := ToString(Smile)
    Print("{S.Length}")
    Cs:[]char32 = array{A, E, Euro, Smile, Last}
    for (C : Cs) { Print("{ToString(C).Length}") }
    if (A < E, E <= Euro, Smile > Euro, A <> E) then Print("ordered")
    if (A = 0u41) then Print("equal")
    Print("{Next(A)}")
    case (Euro):
        0u20AC => Print("euro")
        _ => Print("other")
    var V:char32 = 0u0
    set V = 0u7F
    Print("{ToString(V).Length}")
