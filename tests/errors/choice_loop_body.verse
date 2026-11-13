# expect: 5:46: a choice (a | b) cannot be lifted from here, for now (#208): not from the body of a loop, which takes no choice
# (#283) A choice in a loop's body, in a block lifted into a for's clauses: the loop takes no
# choice, and nothing is lifted out of its body.
Main()<transacts>:void =
    for (X := 1..2, V := block{ loop { Y := 1 | 2; break }; 3 }) { Print("{V}") }
