# Choices inside a block (#283): the block's clauses become the consumer's,
# its names renamed for the place, its last expression the value
Main()<transacts>:void =
    for (X := block{ Y := 1 | 2; Y * 10 }):
        Print("{X}")
    # nested blocks; a block's own choice runs where it is
    for (X := block{ A := 1 | 2; B := block{ C := 10 | 20; C + A }; B * 100 }):
        Print("{X}")
    # a var of the block's own
    for (X := block{ var V : int = 1 | 2; set V += 10; V }):
        Print("{X}")
    # in a first-success context, what a failed alternative did is undone
    var C : int = 0
    if (X := block{ set C += 1; Y := 1 | 2 | 3; set C += 100; Y > 1; Y }):
        Print("{X} {C}")
    Print("{C}")
    # let(…){…} is a block too
    for (X := let(A := 1 | 2){ A * 3 }):
        Print("{X}")
    # first{…} and option{…} keep their choices: they take them
    for (Y := first{ X := 1 | 2 | 3; X > 1; X * 10 }):
        Print("first {Y}")
    if (Z := option{ block{ X := 1 | 2; X > 1; X } }?):
        Print("option {Z}")
