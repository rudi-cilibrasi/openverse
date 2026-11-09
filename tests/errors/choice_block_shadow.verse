# expect: 4:21: 'Y' is already defined; Verse does not allow shadowing
Main()<transacts>:void =
    Y := 5
    for (X := block{ Y := 1 | 2; Y * 10 }):
        Print("{X}")
