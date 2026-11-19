# a class whose added type parameter is comparable, dispatched to by code
# that opens it (#209)
ex(t:type) := class<abstract>:
    Eval()<transacts>:t
lit := class(ex(int)):
    V:int
    Eval<override>()<transacts>:int = V
eqE(a:subtype(comparable)) := class(ex(logic)):
    L:ex(a)
    R:ex(a)
    Eval<override>()<transacts>:logic = logic{L.Eval() = R.Eval()}
Run(E:ex(logic))<transacts>:logic = E.Eval()
Main():void = Print(if (Run(eqE(int){L := lit{V := 1}, R := lit{V := 1}})?) then "eq" else "ne")
