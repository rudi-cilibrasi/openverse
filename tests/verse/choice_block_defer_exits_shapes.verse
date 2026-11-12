# A break or return that leaves a block with a choice of its own runs the block's
# defer: (#283) wherever in the block it is: in an alternative of a choice, in a
# branch of an if with choices in its branches, in a block that is such a branch,
# in a function with several values inlined into the block's clauses, or in
# <suspends> code.
Three(N:int)<transacts>:int =
    defer: Print("three")
    N | N + 1 | N + 2
Shapes(B:logic)<transacts>:void =
    loop:
        if (X := block{ defer: Print("alternative d"); Y := 2 | 1; Z := (if (Y = 2) then break else 5) | 6; Z }, X > 5) then Print("not reached")
    loop:
        if (X := block{ defer: Print("branch d"); Y := 2 | 1; Z := if (Y = 2) then { break } else { 3 | 4 }; Z }, X > 3) then Print("not reached")
    # (such an if's conditions are a scope of their own, inside the block)
    loop:
        if (X := block{ defer: Print("condition d"); Y := 2 | 1; Z := if (defer: Print("condition's d"), Y = 2, break) then { 3 | 4 } else { 5 | 6 }; Z }, X > 5) then Print("not reached")
    loop:
        for (X := block{ defer: Print("for branch d"); Y := 1 | 2; Z := if (Y = 2) then { break } else { 3 | 4 }; Z }):
            Print("for {X}")
    loop:
        if (X := (if (B?) then { defer: Print("block branch d"); Y := 1 | 2; if (Y = 2) then break; Y } else { 7 | 8 }), X > 5) then Print("not reached")
    loop:
        if (X := block{ defer: Print("inlined d"); Y := Three(1); if (Y = 2) then break; Y }, X > 5) then Print("not reached")
Waits()<suspends>:int =
    defer: Print("waits function")
    loop:
        Sleep(0.0)
        if (X := block{ defer: Print("waits break d"); Y := 1 | 2; if (Y = 2) then break; Y }, X > 5) then Print("not reached")
    Sleep(0.0)
    if (X := block{ defer: Print("waits return d"); Y := 1 | 2; if (Y = 2) then return 5; Y }, X > 5) then Print("not reached")
    0
Main()<suspends>:void =
    Shapes(true)
    Print("waits {Waits()}")
