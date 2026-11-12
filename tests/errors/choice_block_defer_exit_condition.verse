# expect: 6:64: defer: cannot be a clause of an if condition or first{…} that has a choice (#208)
# A defer: in the conditions of an if that have a choice of their own is refused (#208),
# also inside a block with a defer: and a choice of its own, with a break that leaves both.
Main()<transacts>:void =
    loop:
        if (X := block{ defer: Print("d"); Y := 2 | 1; Z := if (defer: Print("c"), W := 1 | 2, W = Y, break) then { 3 | 4 } else { 5 | 6 }; Z }, X > 5) then Print("then")
        break
