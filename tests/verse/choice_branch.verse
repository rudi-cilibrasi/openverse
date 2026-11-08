# a choice in the branches of an if (#235): the branch the conditions pick,
# once, then its alternatives; names a condition binds are seen in its branch
Main():void =
    var N:int = 3
    for (X := if (N > 2) then (1 | 2) else (10 | 20)) { Print("a {X}") }
    for (X := if (N > 5) then (1 | 2) else (10 | 20)) { Print("b {X}") }
    for (X := if (N > 5) then 1 else if (N > 2) then (7 | 8) else 9) { Print("c {X}") }
    if (Y := (if (N > 2) then (1 | 2) else 3) + 10, Y > 11) then Print("d {Y}")
    # names the condition binds are visible in its branch
    M:?int = option{5}
    for (Z := if (V := M?) then (V | V * 10) else 0) { Print("e {Z}") }
    # the condition runs once, even with several alternatives
    if (W := if (Print("cond"); N > 2) then (1 | 2 | 3) else 0, W = 3) then Print("f {W}")
    # in a for, with a range before
    for (I := 1..2, Z := if (I = 1) then (I | 100) else -I) { Print("g {Z}") }
