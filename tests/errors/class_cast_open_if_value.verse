# expect: the cast opens pairE's type argument a for its branch, whose value, a ?expr(a'), would name what is unknown outside it, where the if's value is a logic (#250)
# (#250) the value of an if whose cast opens type arguments, a ?expr(a'), would
# leave the if at a type no code outside can name (an existential)
expr(t:type) := class<abstract>:
    Tag():string
lit := class(expr(int)):
    V:int
    Tag<override>():string = "lit"
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Tag<override>():string = "pair"
LeftTag(E:expr(t) where t:type):string =
    X := if (P := pairE[E]) then option{P.L} else false
    if (L := X?) then L.Tag() else "none"
Main():void =
    Print(LeftTag(pairE(int, int){L := lit{V := 4}, R := lit{V := 5}}))
