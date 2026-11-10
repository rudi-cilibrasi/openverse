# Two or more composed or exclusive choices in a for's clauses (#335, phase
# 2): the values in order; a failure in the clauses after a choice before
# any generator undoes the alternative's own last clauses, a later
# generator that gives nothing keeps them; in a generic function whose
# clauses or body write its type parameter, copied
Two(X:int)<transacts>:int = X | X + 1
P(T:string, X:int)<transacts>:int =
    Print(T)
    X | X + 1
F(X:int)<transacts>:int =
    if (X < 0):
        return 0
    X | X + 1
TwoU():int = 1 | 2
GF(I:t where t:type):int =
    R := for (X := (TwoU() | TwoU()), Y := (TwoU() | TwoU())):
        E:[]t = array{}
        X + Y + E.Length
    R.Length
GI(I:t where t:type):int =
    if (X := (TwoU() | TwoU()), Y := (TwoU() | TwoU()), E:[]t = array{}, X + Y + E.Length > 3) then X + Y else 0
Main()<transacts>:void =
    for (A := F(1), B := F(2), C := F(3), A + B + C > 7):
        Print("a {A} {B} {C}")
    for (X := (Two(1) | Two(10)), Y := (Two(100) | Two(200)), X + Y > 210):
        Print("b {X} {Y}")
    # (the clauses after X fail before any generator: X's own prints undone
    # back to its generator, as in one filter)
    for (X := (P("p", 1) | P("q", 2)), Print("after {X}"), Y := F(-1), Z := F(-2), Y + Z > 5):
        Print("never")
    # (a later generator gives nothing: what came before it stays)
    for (X := (P("r", 1) | P("s", 2)), Print("then {X}"), Y := (Two(5) | Two(6)), Z := F(-1), X + Y + Z > 99):
        Print("never")
    Print("end")
    Print("g {GF(7)} {GF("s")} {GI(7)} {GI("s")}")
