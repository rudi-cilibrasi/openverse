# Casts that open (#250), nested: the inner branch uses a value whose type
# mentions the outer cast's opened type; a new object built at opened types
# and a method called on it; casts in a for and with an object that is no local.
expr(t:type) := class<abstract>:
    Tag():string
lit := class(expr(int)):
    V:int
    Tag<override>():string = "lit"
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Tag<override>():string = "pair"
Eval(E:expr(t) where t:type):t =
    if (L := lit[E]) then L.V
    else if (P := pairE[E]) then (Eval(P.L), Eval(P.R))
    else Err()
# nested opening: the inner branch mentions the outer opened a, b
Left(E:expr(t) where t:type):int =
    if (P := pairE[E]):
        if (Q := pairE[P.L]) then 10 + Count(Q.L) + Count(P.R) else 1
    else:
        0
Count(E:expr(t) where t:type):int =
    if (L := lit[E]) then 1
    else if (P := pairE[E]) then Count(P.L) + Count(P.R)
    else 0
Flip(E:expr(t) where t:type):string =
    if (P := pairE[E]):
        Q := Rebuild(P.R, P.L)
        Q.Tag()
    else:
        "no"
Rebuild(L:expr(a), R:expr(b) where a:type, b:type):expr(tuple(a, b)) = pairE(a, b){L := L, R := R}
Get(Es:[]expr(t) where t:type):int =
    Ns := for (E : Es):
        if (P := pairE[E]) then 1 else 0
    Ns.Length
Main():void =
    I:expr(tuple(tuple(int, int), int)) = pairE(tuple(int, int), int){L := pairE(int, int){L := lit{V := 1}, R := lit{V := 2}}, R := lit{V := 3}}
    Print("{Left(I)}")
    E:expr(tuple(int, int)) = pairE(int, int){L := lit{V := 1}, R := lit{V := 2}}
    Print("{Flip(E)}")
    Print("{Get(array{E, E})}")
    Print("{if (P := pairE[(Print("recv"); E)]) then "yes" else "no"}")
