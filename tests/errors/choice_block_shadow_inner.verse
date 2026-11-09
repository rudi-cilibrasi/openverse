# expect: 3:46: 'Y' is already defined
Main()<transacts>:void =
    for (X := block{ Y := 1 | 2; if (Y > 0) { Y := 3 }; Y }):
        Print("{X}")
