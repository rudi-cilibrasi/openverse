# After clauses with effects (#243), a later refining cast of an object
# computed among the moved clauses (by a call, or from the first cast's
# object) is cast again in the then-branch or body from that object, bound
# to a name of its own first, so the branch is typed under its refinement
# too; one whose object may name type arguments a cast opens keeps its name
# only, as its value.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
holder(c:type, d:type) := class:
    Inner:pair(c, d)
hdup(t:type) := class(holder(t, t)):
    K:int = 1
Mk(P:pair(c, d) where c:type, d:type)<transacts><decides>:pair(c, d) =
    Print("mk")
    P
ByCall(P:pair(a, b), Q:pair(c, d) where a:type, b:type, c:type, d:type)<transacts>:?tuple(b, d) =
    if (Print("x"), D := dup[P], R := Mk[Q], E := dup[R]) then option{(D.A, E.A)} else false
ByField(H:holder(c, d) where c:type, d:type)<transacts>:?d =
    if (Print("y"), G := hdup[H], E := dup[G.Inner]) then option{E.A} else false
InFor(Hs:[]holder(c, d) where c:type, d:type)<transacts>:[]d =
    for (H : Hs, (Print("z"); true?), G := hdup[H], E := dup[G.Inner]):
        E.A
expr(t:type) := class<abstract>:
    Tag():string
lit := class(expr(int)):
    V:int
    Tag<override>():string = "lit"
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Tag<override>():string = "pair"
# the object of the second cast names a type argument the first opens
Left(E:expr(t) where t:type)<transacts>:int =
    if (Print("o"), P := pairE[E], L := lit[P.L]) then L.V else -1
Main()<transacts>:void =
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Q:pair(string, string) = dup(string){A := "q", B := "r"}
    if (V := ByCall(Y, Q)?) then Print("ByCall {V(0)} {V(1)}")
    Z:pair(string, string) = pair(string, string){A := "q", B := "r"}
    if (V := ByCall(Y, Z)?) then Print("ByCall") else Print("ByCall no")
    H1:holder(int, int) = hdup(int){Inner := dup(int){A := 7, B := 8}}
    H2:holder(int, int) = hdup(int){Inner := pair(int, int){A := 7, B := 8}}
    if (V := ByField(H1)?) then Print("ByField {V}")
    if (V := ByField(H2)?) then Print("ByField {V}") else Print("ByField no")
    R := InFor(array{H1, H2, H1})
    Print("InFor {R.Length}")
    X:expr(tuple(int, int)) = pairE(int, int){L := lit{V := 1}, R := lit{V := 2}}
    Print("Left {Left(X)} {Left(lit{V := 3})}")
