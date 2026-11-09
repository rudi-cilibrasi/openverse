# leading refining casts, two and three, each on what the one before gives: the if of the rest has a cast as its first clause, lifted too (#243 follow-up, review of #277)
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
# two leading refining casts, the second on what the first gives, then a clause
Deep(E:expr(t) where t:type):int =
    if (P := pairE[E], Q := pairE[P.L], X := Q.R.Eval()) then 1 else 0
Three(E:expr(t) where t:type):int =
    if (P := pairE[E], Q := pairE[P.L], S := pairE[Q.L]) then 3 else 0
Main():void =
    Inner := pairE(int, int){L := lit{V := 1}, R := lit{V := 2}}
    Print("{Deep(pairE(tuple(int, int), int){L := Inner, R := lit{V := 3}})} {Deep(Inner)} {Deep(lit{V := 0})}")
    Print("{Three(pairE(tuple(tuple(int, int), int), int){L := pairE(tuple(int, int), int){L := Inner, R := lit{V := 3}}, R := lit{V := 4}})} {Three(Inner)}")
