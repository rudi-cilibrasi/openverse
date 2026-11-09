# Casts that refine, in methods (#243): the branch reads Self's fields, calls
# its methods and sets its var fields by their bare names, in a class and in a
# generic class.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
expr(t:type) := class<abstract>:
    Tag():string
lit := class(expr(int)):
    V:int
    Tag<override>():string = "lit"
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Tag<override>():string = "pair"
evaluator := class:
    var Calls:int = 0
    Base:int = 100
    Bump()<transacts>:void = set Calls += 1
    Ev(E:expr(t) where t:type)<transacts>:t =
        Bump()
        if (L := lit[E]):
            set Calls += 10
            L.V + Base
        else if (P := pairE[E]) then (Ev(P.L), Ev(P.R))
        else Err()
holder(t:type) := class:
    X:t
    Same(P:pair(t, u) where u:type):u =
        if (D := dup[P]) then X else P.B
    Get(P:pair(a, b), Y:a where a:type, b:type):b =
        if (D := dup[P]) then Y else P.B
# (a field named like a built-in is the built-in when called, in the branch
# as outside it)
Two(X:int, Y:int):int = X * 10 + Y
host := class:
    Max:type{_(:int, :int):int} = Two
    F(P:pair(a, b) where a:type, b:type):string =
        Out := Max(7, 3)
        In := if (D := dup[P]) then Max(7, 3) else 0
        "{Out} {In}"
Main():void =
    Print(host{}.F(dup(int){A := 1, B := 2}))
    V := evaluator{}
    R := V.Ev(pairE(int, int){L := lit{V := 1}, R := lit{V := 2}})
    Print("{R(0)} {R(1)} calls {V.Calls}")
    H := holder(int){X := 7}
    Print("{H.Same(dup(int){A := 1, B := 2})} {H.Same(pair(int, int){A := 1, B := 2})}")
    Print("{H.Get(dup(string){A := "a", B := "b"}, "y")}")
