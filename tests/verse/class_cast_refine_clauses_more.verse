# refining casts as the first clause: clauses after them binding names, a choice among them, an if without else, a condition that only the cast makes failable (#243 follow-up)
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
# the cast, then clauses that use it, a choice among them, and no else
Swap(E:expr(t) where t:type):?t =
    if (P := pairE[E], X := P.L.Eval(), Y := (1 | 2), Y > 1) then option{(X, P.R.Eval())} else false
Show(E:expr(t) where t:type):void =
    if (P := pairE[E], X := P.L.Eval()):
        Print("a pair")
Main():void =
    E := pairE(int, int){L := lit{V := 4}, R := lit{V := 5}}
    if (S := Swap(E)?) then Print("{S(0)} {S(1)}")
    Show(E)
    Show(lit{V := 1})
    if (Q := Swap(lit{V := 1})?) then Print("no") else Print("not a pair")
