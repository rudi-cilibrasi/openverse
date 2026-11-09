# Casts that open existential type arguments (#250): an evaluator matching
# pairE and fstE, whose a and b the branch has no names for.
expr(t:type) := class<abstract>:
    Tag():string
lit := class(expr(int)):
    V:int
    Tag<override>():string = "lit"
add := class(expr(int)):
    L:expr(int)
    R:expr(int)
    Tag<override>():string = "add"
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Tag<override>():string = "pair"
fstE(a:type, b:type) := class(expr(a)):
    P:expr(tuple(a, b))
    Tag<override>():string = "fst"
Eval(E:expr(t) where t:type):t =
    if (L := lit[E]) then L.V
    else if (A := add[E]) then Eval(A.L) + Eval(A.R)
    else if (P := pairE[E]) then (Eval(P.L), Eval(P.R))
    else if (F := fstE[E]) then Eval(F.P)(0)
    else Err()
Main():void =
    E:expr(tuple(int, int)) = pairE(int, int){L := lit{V := 1}, R := add{L := lit{V := 2}, R := lit{V := 3}}}
    R := Eval(E)
    Print("{R(0)} {R(1)}")
    F:expr(int) = fstE(int, int){P := pairE(int, int){L := lit{V := 7}, R := lit{V := 8}}}
    Print("{Eval(F)}")
