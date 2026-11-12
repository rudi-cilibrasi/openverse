# Casts in failure contexts other than an if's first clauses (#243), with an
# interface as a GADT's root, a cast that opens type arguments (#250), and
# one from an interface referred to through views (#351): evaluation by
# <decides> helpers, one per class, instead of an if chain.
expr(t:type) := interface:
    Show():string
lit := class(expr(int)):
    V:int
    Show<override>():string = "{V}"
add := class(expr(int)):
    L:expr(int)
    R:expr(int)
    Show<override>():string = "({L.Show()}+{R.Show()})"
isz := class(expr(logic)):
    E:expr(int)
    Show<override>():string = "isz({E.Show()})"
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Show<override>():string = "<{L.Show()},{R.Show()}>"
AsLit(E:expr(t) where t:type)<decides>:t =
    L := lit[E]
    L.V
AsAdd(E:expr(t) where t:type)<decides>:t =
    A := add[E]
    Eval(A.L) + Eval(A.R)
AsIsz(E:expr(t) where t:type)<decides>:t =
    Z := isz[E]
    logic{Eval(Z.E) = 0}
# (t is tuple(a', b') here, a' and b' the types the cast opens)
AsPair(E:expr(t) where t:type)<decides>:t =
    P := pairE[E]
    (Eval(P.L), Eval(P.R))
Eval(E:expr(t) where t:type):t =
    if (V := AsLit[E]) then V
    else if (V := AsAdd[E]) then V
    else if (V := AsIsz[E]) then V
    else if (V := AsPair[E]) then V
    else Err()
# option{…} and a for's clauses
Lit(E:expr(t) where t:type):?t = option{L := lit[E]; L.V + 100}
Lits(Es:[]expr(t) where t:type):[]t = for (E : Es, L := lit[E]) { L.V }
# views (#351): a reference to an interface a class gives other type arguments
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Put(X:u):int
one(u:type) := class(sink(u)):
    W:u
    Put<override>(X:u):int = 100
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Put<override>(X:u):int = 1
OneW(S:sink(string))<transacts>:?string = option{Print("v"); O := one[S]; O.W}
Main()<transacts>:void =
    E1:expr(int) = add{L := lit{V := 2}, R := lit{V := 3}}
    Print("{E1.Show()} = {Eval(E1)}")
    E2:expr(logic) = isz{E := add{L := lit{V := 0}, R := lit{V := 0}}}
    Print("{E2.Show()} = {if (Eval(E2)?) then "true" else "false"}")
    E3:expr(tuple(int, logic)) = pairE(int, logic){L := E1, R := E2}
    R3 := Eval(E3)
    Print("{E3.Show()} = ({R3(0)}, {if (R3(1)?) then "true" else "false"})")
    if (X := Lit(lit{V := 5})?) then Print("Lit {X}")
    if (X := Lit(E1)?) then Print("Lit {X}") else Print("Lit no")
    Print("Lits {Lits(array{lit{V := 1}, E1, lit{V := 3}}).Length}")
    S1:sink(string) = one(string){W := "w"}
    S2:sink(string) = both(int, string){V := 3}
    if (W := OneW(S1)?) then Print("OneW {W}")
    if (W := OneW(S2)?) then Print("OneW {W}") else Print("OneW no")
