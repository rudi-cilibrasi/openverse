# Casts that refine (#243): a type-equality witness, comparable type
# parameters, a struct and a function value used in the branch, a cast in a
# for's body and in option{}, and two casts binding one name.
eqw(a:type, b:type) := class<abstract>:
    Id():int
refl(t:type) := class(eqw(t, t)):
    Id<override>():int = 1
# (a type-equality witness: an a is a b through it)
Coerce(W:eqw(a, b), X:a where a:type, b:type):b =
    if (R := refl[W]) then X else Err()
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
pt(t:type) := struct:
    X:t
    Y:t
# (comparable type parameters, a struct and a function value captured)
Eq(P:pair(a, b), V:pt(a), F:type{_(:a)<computes>:a}, X:a where a:subtype(comparable), b:subtype(comparable))<decides>:b =
    if (D := dup[P]):
        G := F(V.X)
        G = X
        G
    else:
        P.B
Inc(N:int)<computes>:int = N + 1
# (in a for's body, in option{}, two casts binding one name)
Sum(Ps:[]pair(a, b), X:a where a:type, b:type):[]b =
    for (P : Ps):
        if (D := dup[P]) then X else P.B
Maybe(P:pair(a, b), X:a where a:type, b:type):?b =
    option{if (D := dup[P]) then X else P.B}
Twice(P:pair(a, b), Q:pair(a, b), X:a where a:type, b:type):tuple(b, b) =
    L := if (D := dup[P]) then X else P.B
    R := if (D := dup[Q]) then X else Q.B
    (L, R)
Main():void =
    Print("coerced {Coerce(refl(int){}, 5)}")
    if (V := Eq[dup(int){A := 1, B := 1}, pt(int){X := 4, Y := 0}, Inc, 5]) then Print("eq {V}")
    if (V := Eq[dup(int){A := 1, B := 1}, pt(int){X := 4, Y := 0}, Inc, 6]) then Print("eq {V}") else Print("not eq")
    Xs := Sum(array{dup(int){A := 1, B := 2}, pair(int, int){A := 3, B := 4}}, 9)
    Print("{Xs[0] or -1} {Xs[1] or -1}")
    Print("{Maybe(dup(int){A := 1, B := 2}, 8)? or -1}")
    T := Twice(dup(int){A := 1, B := 2}, pair(int, int){A := 3, B := 4}, 7)
    Print("{T(0)} {T(1)}")
