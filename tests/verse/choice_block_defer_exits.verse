# A break or return that leaves a block with a choice of its own runs the block's
# defer: (#283), as it does for a block without one: in an if's condition, first{},
# option{}, a for's clauses, and an if in a for's body. A value that the clauses
# after the block reject runs it too, and is rolled back with it.
Breaks()<transacts>:void =
    loop:
        if (X := block{ defer: Print("if d"); Y := 1 | 2; if (Y = 2) then break; Y }, X > 5) then Print("not reached")
    loop:
        if (X := block{ defer: Print("if, no choice d"); Y := 2; if (Y = 2) then break; Y }, X > 5) then Print("not reached")
    loop:
        if (Z := first{ X := block{ defer: Print("first d"); Y := 1 | 2; if (Y = 2) then break; Y }; X > 5; X }) then Print("not reached")
    loop:
        R := option{ X := block{ defer: Print("option d"); Y := 1 | 2; if (Y = 2) then break; Y }; X > 5; X }
    loop:
        for (X := block{ defer: Print("for d"); Y := 1 | 2; if (Y = 2) then break; Y }):
            Print("for {X}")
Returns(K:int)<transacts>:int =
    defer: Print("function d")
    if (K = 0, X := block{ defer: Print("if d"); Y := 1 | 2; if (Y = 2) then return 10; Y }, X > 5) then Print("not reached")
    if (K = 1, Z := first{ X := block{ defer: Print("first d"); Y := 1 | 2; if (Y = 2) then return 11; Y }; X > 5; X }) then Print("not reached")
    if (K = 2):
        R := option{ X := block{ defer: Print("option d"); Y := 1 | 2; if (Y = 2) then return 12; Y }; X > 5; X }
    if (K = 3):
        for (X := block{ defer: Print("for d"); Y := 1 | 2; if (Y = 2) then return 13; Y }):
            Print("for {X}")
    for (I := 1..2):
        if (X := block{ defer: Print("body d {I}"); Y := I | 5; if (Y = 2) then return 14; Y }, X > 5) then Print("not reached")
        Print("body {I}")
    0
Main()<transacts>:void =
    Breaks()
    for (K := 0..4):
        Print("returned {Returns(K)}")
