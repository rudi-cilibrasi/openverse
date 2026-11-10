# expect: 4:61: unknown identifier 'Q'
# (a block's defer: runs after its value once lifted, #283, but still cannot use a name declared after it)
Main()<transacts>:void =
    for (I := 1..2, X := (if (I = 1) then { defer: Print("t {Q}"); Z := 1 | 2; Q := Z; Q } else 0)) { Print("v {X}") }
