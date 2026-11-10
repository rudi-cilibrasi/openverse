# Calls of functions with several values, recursive or not, and choices
# inside a branch's expression, in an if's branches (#283): the if picks
# one branch, once (#331), whose values are then the call's or the choice's
Two(N : int):int = N | N + 10
Down(N : int):int = if (N > 0) then (N | Down(N - 1)) else 0
Opt(N : int):?int = option{N} | false
P(S : string)<transacts>:int =
    Print(S)
    1
Main()<transacts>:void =
    # in a for: a call, a recursive call, a choice inside an expression
    for (C := 0..1, X := (if (C = 0) then Two(2) else 7)):
        Print("a {C} {X}")
    for (C := 0..1, X := (if (C = 0) then Down(2) else 7)):
        Print("b {C} {X}")
    for (C := 0..1, X := (if (C = 0) then 10 + (1 | 2) else Two(C))):
        Print("c {C} {X}")
    # where the first success is taken
    if (Y := (if (1 = 1) then Down(2) else 7), Y < 1):
        Print("d {Y}")
    if (Y := (if (1 = 2) then Down(2) else Two(5)), Y > 10):
        Print("e {Y}")
    # names the condition binds, in the call's arguments; else if
    M : ?int = option{3}
    for (Z := if (V := M?) then Two(V) else 0):
        Print("f {Z}")
    for (C := 0..2, Z := if (C = 0) then 0 else if (C = 1) then Two(C) else Down(C)):
        Print("g {C} {Z}")
    # a plain branch picked and rejected undoes what came before; a call's
    # choice is a generator, which keeps it
    for (A := P("h"), Z := (if (A > 0) then 0 else Two(1)), Z > 5):
        Print("never")
    for (A := P("i"), Z := (if (A > 5) then 0 else Two(1)), Z > 5):
        Print("i {Z}")
    # with no type written, the branches' join
    for (C := 0..1, Z := (if (C = 0) then Opt(4) else false)):
        if (V := Z?) then Print("j {C} {V}") else Print("j {C} none")
