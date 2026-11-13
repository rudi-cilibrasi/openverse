# expect: 5:68: a range a..b can only be the source of a for clause
# (#283) A block as a branch, lifted with the if: a range it binds stays an expression, an error
# (a range is only a for's iterated expression), not a generator of the for.
Main()<transacts>:void =
    for (C := 1..2, X := if (C = 1) then block{ Y := (1 | 2); Z := 1..3; Y * 10 } else 7) { Print("{X}") }
