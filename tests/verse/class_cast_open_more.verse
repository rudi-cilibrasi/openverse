# Casts that open (#250): comparable opened parameters (compared in the
# branch), an abstract target, and a target whose opened parameters an
# ancestor adds, with no override below that ancestor.
expr(t:type) := class<abstract>:
    Id:int = 0
lit := class(expr(int)):
    V:int
eqE(a:subtype(comparable)) := class(expr(logic)):
    X:a
    Y:a
holderA(a:type) := class<abstract>(expr(int)):
    V:a
holderB(a:type) := class(holderA(a)):
    W:int = 4
pairNo(a:type, b:type) := class<abstract>(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
tagged(a:type, b:type, n:type) := class(pairNo(a, b)):
    Note:n
Truth(E:expr(t) where t:type):logic =
    if (Q := eqE[E]) then (if (Q.X = Q.Y) then true else false) else false
Num(E:expr(t) where t:type):int =
    if (H := holderA[E]) then 40
    else if (T := tagged[E]) then 100 + Num(T.L) + Num(T.R)
    else if (L := lit[E]) then L.V
    else 0
Main():void =
    E:expr(logic) = eqE(int){X := 3, Y := 3}
    F:expr(logic) = eqE(string){X := "a", Y := "b"}
    Print("{if (Truth(E)?) then "eq" else "ne"} {if (Truth(F)?) then "eq" else "ne"}")
    G:expr(int) = holderB(string){V := "v"}
    T:expr(tuple(int, int)) = tagged(int, int, string){L := lit{V := 1}, R := lit{V := 2}, Note := "n"}
    Print("{Num(G)} {Num(T)}")
