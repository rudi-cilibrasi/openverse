# An if's branches, and a choice's alternatives, join the same in either
# order (#366): with nothing in common, each later one's type is tried
# for them all, so a bare false first joins an option as the empty option
Opt(N : int):?int = option{N} | false
Main()<transacts>:void =
    C := 0
    Y := if (C = 1) then false else option{4}
    if (V := Y?) then Print("a {V}")
    Z := if (C = 0) then option{4} else false
    if (V := Z?) then Print("b {V}")
    for (X := (false | option{5})):
        if (V := X?) then Print("c {V}") else Print("c none")
    for (X := (if (C = 1) then false else (option{6} | false))):
        if (V := X?) then Print("d {V}") else Print("d none")
    if (X := (if (C = 1) then false else (option{7} | false)), V := X?):
        Print("e {V}")
    for (X := (if (C = 1) then false else Opt(8))):
        if (V := X?) then Print("f {V}") else Print("f none")
    if (X := (if (C = 1) then false else Opt(9)), V := X?):
        Print("g {V}")
    W := if (C = 0) then 1 else 2.5
    Print("h")
    A := if (C = 1) then array{} else array{4, 5}
    Print("i {A.Length}")
    for (X := (array{} | array{6})):
        Print("j {X.Length}")
    for (X := (if (C = 1) then array{} else (array{7} | array{}))):
        Print("k {X.Length}")
