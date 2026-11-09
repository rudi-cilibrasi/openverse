# Two or more composed choices where the first success is taken (#335): the
# clauses after each compiled once, as a function of their own that each
# alternative calls, not copied into each. The first success in spatial
# order (back into an alternative's own values first), failed attempts
# undone, a var set in the clauses after a choice (copied in and out), a
# field set in a method's (Self), two and three levels
Two(X:int)<transacts>:int = X | X + 1
P(T:string, X:int)<transacts>:int =
    Print(T)
    X | X + 1
counter := class:
    var N : int = 0
    Find()<transacts>:int =
        if (X := (Two(1) | Two(2)), set N += 1, Y := (Two(10) | Two(20)), X + Y > 22):
            X + Y
        else:
            -1
Main()<transacts>:void =
    if (X := (Two(1) | Two(2)), Y := (Two(10) | Two(20)), Z := (Two(100) | Two(200)), X + Y + Z > 212):
        Print("a {X} {Y} {Z}")
    if (X := (Two(1) | Two(2)), Y := (Two(10) | Two(20)), Z := (Two(100) | Two(200)), X + Y + Z > 223):
        Print("b {X} {Y} {Z}")
    if (X := (Two(1) | Two(2)), Y := (Two(10) | Two(20)), Z := (Two(100) | Two(200)), X + Y + Z > 999):
        Print("never")
    else:
        Print("c none")
    if (X := (P("p", 1) | P("q", 2)), Y := (P("r", 10) | P("s", 20)), Z := (P("t", 100) | P("u", 200)), X + Y + Z > 223):
        Print("d {X} {Y} {Z}")
    var V : int = 0
    if (X := (Two(1) | Two(2)), set V += 1, Y := (Two(10) | Two(20)), X + Y > 22):
        Print("e {X} {Y} {V}")
    Print("v {V}")
    C := counter{}
    Print("f {C.Find()} {C.N}")
