# expect: (the cast that binds L is not repeated where the clauses' names are used, as its object may name type arguments a cast before it opens and is not read from that cast's name by fields that are no vars (#250))
# (#250) a later cast whose object is read from an opening cast's name through a
# var field: read again, it might be another object, so the branch has no
# refinement of a', which its value needs
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
vpair(a:type, b:type) := class(expr(tuple(a, b))):
    var L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Lits(E:expr(t) where t:type):?t =
    if (Print("try "), P := vpair[E], L := lit[P.L], R := lit[P.R]) then option{(L.V, R.V)} else false
Main():void = Print("ok")
