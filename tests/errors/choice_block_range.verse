# expect: 5:39: a range a..b can only be the source of a for clause
# (#283) A block's clauses are lifted into a for's with a choice in it, but a range in it stays an
# expression: only a for's iterated expression may be one (the Book of Verse's rule).
Main()<transacts>:void =
    for (X := block{ Y := 1 | 2; R := Y..3 }):
        Print("r {X}")
