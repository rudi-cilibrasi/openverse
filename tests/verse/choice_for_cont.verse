# Two or more composed or exclusive choices in a for's clauses (#335, phase
# 2): the values in order; the clauses are one search (#761), so an
# alternative none of whose rows reaches the body is undone with its own
# clauses, whether the clauses after it fail before a generator or a later
# generator gives nothing; in a generic function whose clauses or body
# write its type parameter too
Two(X:int)<transacts>:int = X | X + 1
P(T:string, X:int)<transacts>:int =
    Print(T)
    X | X + 1
F(X:int)<transacts>:int =
    if (X < 0):
        return 0
    X | X + 1
TwoU():int = 1 | 2
GF(I:t where t:type)<transacts>:int =
    R := for (X := (TwoU() | TwoU()), Y := (TwoU() | TwoU())):
        E:[]t = array{}
        X + Y + E.Length
    R.Length
GI(I:t where t:type)<transacts>:int =
    if (X := (TwoU() | TwoU()), Y := (TwoU() | TwoU()), E:[]t = array{}, X + Y + E.Length > 3) then X + Y else 0
Main()<transacts>:void =
    for (A := F(1), B := F(2), C := F(3), A + B + C > 7):
        Print("a {A} {B} {C}")
    for (X := (Two(1) | Two(10)), Y := (Two(100) | Two(200)), X + Y > 210):
        Print("b {X} {Y}")
    # (the clauses after X fail before any generator: no row reaches the
    # body, so nothing is printed, P's prints included)
    for (X := (P("p", 1) | P("q", 2)), (Print("after {X}"); true?), Y := F(-1), Z := F(-2), Y + Z > 5):
        Print("never")
    # (a later generator gives nothing: no row reaches the body here either,
    # and what came before it is undone with the rows)
    for (X := (P("r", 1) | P("s", 2)), (Print("then {X}"); true?), Y := (Two(5) | Two(6)), Z := F(-1), X + Y + Z > 99):
        Print("never")
    Print("end")
    Print("g {GF(7)} {GF("s")} {GI(7)} {GI("s")}")
