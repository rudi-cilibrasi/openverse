# Mutually recursive functions with several values, taken lazily (#283):
# one stack of items for the strongly connected group, tagged by function,
# so an infinite one gives its values one at a time
Evens(N : int):int = N | Odds(N + 1)
Odds(N : int):int = Evens(N + 1)
Walk(N : int, S : string):string = if (N > 2) then S else (S | Hop(N + 1, S + "a"))
Hop(N : int, T : string):string = if (N > 2) then T + "!" else (Walk(N + 1, T + "b") | T)
P(S : string)<transacts>:int =
    Print(S)
    1
Up(N : int)<transacts>:int =
    X := P("u{N}")
    if (N > 3) then N else (N | Down(N + 1))
Down(N : int)<transacts>:int =
    X := P("d{N}")
    if (N > 3) then -N else Up(N + 1)
Main()<transacts>:void =
    # (infinite: the first success takes what it needs)
    if (X := Evens(0), X > 7):
        Print("a {X}")
    for (S := Walk(0, "")):
        Print("b {S}")
    # (effect-free, where the first success is taken)
    if (S := Walk(0, ""), S = "ab"):
        Print("c {S}")
    # (with effects, in a for and where the first success is taken)
    for (X := Up(0)):
        Print("d {X}")
    if (X := Up(0), X > 1):
        Print("e {X}")
    # (in another for's clauses)
    for (I := 0..1, X := Up(I + 2)):
        Print("f {I} {X}")
