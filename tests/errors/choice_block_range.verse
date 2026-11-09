# expect: 3:28: a choice (a | b) cannot be lifted from a block that binds a range
Main()<transacts>:void =
    for (X := block{ Y := 1 | 2; R := Y..3 }):
        Print("r {X}")
