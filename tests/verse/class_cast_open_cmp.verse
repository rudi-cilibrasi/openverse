# Casts that open (#250): an opened parameter that a comparable type
# parameter's refinement mentions (t:subtype(comparable) refined to
# tuple(a', b')) is comparable, as the object's type argument for t is.
ex(t:type) := class<abstract>:
    Eval():t
lit := class(ex(int)):
    V:int
    Eval<override>():int = V
slit := class(ex(string)):
    V:string
    Eval<override>():string = V
pairE(a:type, b:type) := class(ex(tuple(a, b))):
    L:ex(a)
    R:ex(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
optE(a:type) := class(ex(?a)):
    E:ex(a)
    Eval<override>():?a = option{E.Eval()}
Eq(E:ex(t), X:t where t:subtype(comparable)):logic =
    if (P := pairE[E]) then logic{(P.L.Eval(), P.R.Eval()) = X}
    else if (O := optE[E]) then logic{option{O.E.Eval()} = X}
    else logic{E.Eval() = X}
Show(B:logic):string = if (B?) then "eq" else "ne"
Main():void =
    E:ex(tuple(int, string)) = pairE(int, string){L := lit{V := 1}, R := slit{V := "s"}}
    Print("{Show(Eq(E, (1, "s")))} {Show(Eq(E, (1, "t")))}")
    O:ex(?int) = optE(int){E := lit{V := 4}}
    Print("{Show(Eq(O, option{4}))} {Show(Eq(O, false))}")
