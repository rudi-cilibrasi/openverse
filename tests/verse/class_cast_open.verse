# Casts that open (#250): classes below the target that repeat or add type
# arguments, a closed object type, and a branch with a var and locals.
expr(t:type) := class<abstract>:
    Tag():string
lit := class(expr(int)):
    V:int
    Tag<override>():string = "lit"
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Tag<override>():string = "pair"
dupP(a:type) := class(pairE(a, a)):
    N:int = 0
tripleE(a:type, b:type, c:type) := class(pairE(a, b)):
    Extra:c
Count(E:expr(t) where t:type):int =
    if (L := lit[E]) then 1
    else if (P := pairE[E]) then Count(P.L) + Count(P.R)
    else 0
Closed(E:expr(tuple(int, int))):int =
    if (P := pairE[E]) then Count(P.L) + Count(P.R) + 100 else -1
Swap(E:expr(t), X:t where t:type):t =
    if (P := pairE[E]):
        var Seen:int = 0
        Y := P.R
        set Seen += Count(Y)
        X
    else:
        X
Main():void =
    E:expr(tuple(int, int)) = dupP(int){L := lit{V := 1}, R := lit{V := 2}}
    Print("{Count(E)}")
    T:expr(tuple(int, int)) = tripleE(int, int, string){L := lit{V := 1}, R := lit{V := 2}, Extra := "x"}
    Print("{Count(T)}")
    Print("{Closed(E)} {Closed(T)}")
    Print("{Swap(E, (5, 6))(1)}")
