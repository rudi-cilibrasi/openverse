# The clause macros, whose value is a clause list's
# (if{…} else, for{…}, first{…}, first(…){…}, assert{…}).
# The value of a clause list is its last clause's: a binding's name, or the
# expression's value.

# without a body after it, first(…) is still a call
first(X:int, ?By:int = 1):int = X + By

Main():void =
    Xs := array{1, 5, 2, 7}
    # if{c}: c in a failure context (its output too)
    if { Xs[1] > 3; Print("big") }
    if { Xs[9] > 3; Print("not printed") }
    # if{c} else e: c's value when it succeeds, else e's
    A := if { X := Xs[9] } else { 0 }
    B := if { X := Xs[1]; X + 10 } else { 0 }
    C := if { Xs[9] } else if { Xs[3] } else { -1 }
    Print("{A} {B} {C}")
    # for{c}: c's value for each way it succeeds (generators, filters, bindings)
    Ds := for { X := 1..4; X * X }
    Es := for { X : Xs; X > 2 }
    Fs := for { I -> X : Xs; Y := Xs[X] }
    Gs := for {
        X : Xs
        X < 6 }
    if (D3 := Ds[3], E0 := Es[0], F0 := Fs[0], G1 := Gs[1]):
        Print("{Ds.Length} {D3} {Es.Length} {E0} {Fs.Length} {F0} {Gs.Length} {G1}")
    # first{c} fails when c does; first(c){b} runs b with c's names once c succeeds
    if (G := first { Xs[2] }):
        Print("{G}")
    if (H := first(X := Xs[0]; X > 0) { X * 100 }):
        Print("{H}")
    if (first(Xs[9]) { Print("not printed") }) {} else { Print("first failed") }
    Hs := for { X := 0..4; first { Y := Xs[X]; Y * 2 } }
    Print("{Hs.Length}")
    Print("{first(3)}")
    Print("{first(?By := 4, 3)}")
    # a block on the line after a call of first is a statement of its own
    Y := first(1)
    { Print("block {Y}") }
    # a void branch makes the if void, as a statement (void accepts any value)
    if { X := Xs[9] } else { Print("none") }
    if { Xs[9] } else if { Xs[1] > 9 } else { Print("neither") }
    if { Xs[9] } else if { Xs[1] > 1; Print("second") }
    # assert{c}: a runtime error unless c succeeds
    assert { Xs.Length = 4; Xs[0] = 1 }
    Print("asserted")
    assert { Xs[0] = 2 }
    Print("not reached")
