# first takes its clauses as for does: first{c}, first(c){b}, first(c). b,
# first(c) do b, and first: with its clauses indented, then do: (Book of
# Verse tests, FlowControl/first.versetest). Here the clauses choose with
# `|`; a generator in first parses and is not supported yet.
Main():void =
    if:
        A := first{X := (1 | 2 | 3); X > 1}
        B := first(Y := (5 | 6); Y > 5) {Y * 10}
        C := first(Z := (7 | 8); Z > 7). Z + 1
        D := first:
            W := (1 | 4)
            W > 2
        do:
            W * 100
    then:
        Print("{A} {B} {C} {D}")
