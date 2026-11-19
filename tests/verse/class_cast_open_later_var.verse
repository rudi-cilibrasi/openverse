# A mutable field is read once into the selected literal; later writes do not replace that snapshot.
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Lits(E:expr(t) where t:type)<transacts>:?t =
    if (Print("try "), P := vpair[E], L := lit[P.L], set P.L = lit{V:=99}, R := lit[P.R]) then option{(L.V, R.V)} else false
Fail(E:expr(t) where t:type)<transacts>:?t =
    if (Print("try "), P := vpair[E], L := lit[P.L], set P.L = lit{V:=77}, R := lit[P.R], false?) then option{(L.V, R.V)} else false
Main():void =
    P:=vpair(int,int){L:=lit{V:=3},R:=lit{V:=4}}
    if (V := Lits(P)?) then Print("{V(0)} {V(1)} now {P.L.Eval()}") else Print("wrong")
    if (V := Fail(P)?) then Print("wrong") else Print("rollback {P.L.Eval()}")
