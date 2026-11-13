# (#250) a later cast whose object is read by fixed fields from a cast that
# opens type arguments: where the cast takes the clauses after it (the
# clauses before it print), the branch casts again, reading the object again
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
txt := class(expr(string)):
    S:string
    Eval<override>():string = S
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
holder(t:type) := class:
    E:expr(t)
# t = tuple(a', b'), a' = int, b' = string
# (a failed condition undoes its output)
Lits(E:expr(t) where t:type):?t =
    if (Print("try "), P := pairE[E], L := lit[P.L], R := txt[P.R]) then option{(L.V + 1, R.S + "!")} else false
# through a field of a field: t = tuple(tuple(int, b''), b')
Deep(H:holder(t) where t:type):?t =
    if (Print("deep "), P := pairE[H.E], Q := pairE[P.L], L := lit[Q.L]) then option{((L.V * 10, Q.R.Eval()), P.R.Eval())} else false
# in a for, the same: each element's clauses, then the body
Sums(Es:[]expr(t) where t:type):[]t =
    for (E : Es, Print("e "), P := pairE[E], L := lit[P.L], R := lit[P.R]) { (L.V + R.V, R.V) }
Main():void =
    if (V := Lits(pairE(int, string){L := lit{V := 4}, R := txt{S := "s"}})?) then Print("{V(0)} {V(1)}")
    if (V := Lits(pairE(int, int){L := lit{V := 4}, R := lit{V := 5}})?) then Print("no") else Print("not lits")
    if (V := Lits(lit{V := 1})?) then Print("no") else Print("not a pair")
    Inner := pairE(int, string){L := lit{V := 3}, R := txt{S := "in"}}
    if (V := Deep(holder(tuple(tuple(int, string), int)){E := pairE(tuple(int, string), int){L := Inner, R := lit{V := 9}}})?) then
        Print("{V(0)(0)} {V(0)(1)} {V(1)}")
    if (V := Deep(holder(int){E := lit{V := 2}})?) then Print("no") else Print("none")
    Ps := array{pairE(int, int){L := lit{V := 1}, R := lit{V := 2}}, pairE(int, int){L := lit{V := 5}, R := lit{V := 6}}}
    for (V : Sums(Ps)) { Print("{V(0)}/{V(1)} ") }
    Print("")
