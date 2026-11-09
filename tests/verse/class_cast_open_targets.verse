# Casts that open (#250) to targets whose type arguments are not their own
# type parameters as a whole: one that repeats them (dupP), a closed one
# (leafP), and one that gives its parent ?b (w2).
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
dupP(a:type) := class(pairE(a, a)):
    Z:int = 0
leafP := class(pairE(int, string)):
    Y:int = 0
w1(a:type) := class(ex(a)):
    V:a
    Eval<override>():a = V
w2(b:type) := class(w1(?b)):
    Inner:ex(b)
Count(E:ex(t) where t:type):int =
    if (P := dupP[E]) then 10 else 1
Bump(E:ex(t), D:t where t:type):t =
    if (P := leafP[E]) then (P.L.Eval() + 1, P.R.Eval()) else D
Unwrap(E:ex(t), D:t where t:type):t =
    if (W := w2[E]) then option{W.Inner.Eval()} else D
Main():void =
    Print("{Count(dupP(int){L := lit{V := 1}, R := lit{V := 2}})} {Count(lit{V := 3})}")
    R := Bump(leafP{L := lit{V := 1}, R := slit{V := "s"}}, (0, "d"))
    Print("{R(0)} {R(1)}")
    E:ex(?int) = w2(int){V := false, Inner := lit{V := 5}}
    Print("{Unwrap(E, false)? or -1}")
