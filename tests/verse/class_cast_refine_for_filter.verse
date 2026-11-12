# A for's clauses past a generator after a refining cast that use its name
# (#243): each casts the object again where it uses it, a filter as a
# whole, a binding's value (so it still binds its name, which the body,
# cast again, uses), a range's bounds, a set, and each alternative of a
# choice, lifted out of its clause first. An element whose clauses fail,
# its cast's included, is undone.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    Items:[]t = array{}
    C:int = 1
cell := class:
    var N:int = 0
# a filter past the generator that uses the cast
Keep(P:pair(a, b) where a:type, b:type):[]a =
    for (D := dup[P], X : D.Items, D.C > 0) { X }
# a binding past the generator, its name in the body; a range's bound; a set
Sum(H:cell, Ps:[]pair(a, b) where a:type, b:type)<transacts>:[]b =
    for (P : Ps, Print("p"), D := dup[P], X : D.Items, W := D.A, I := 0..D.C, set H.N += D.C, I < 2):
        Print("{I}")
        W
# a choice past the generator, of the cast's, and one inside an expression
Choose(P:pair(a, b) where a:type, b:type):[]int =
    for (D := dup[P], X : D.Items, Y := (D.C | D.C + 10)) { Y }
Nested(P:pair(a, b) where a:type, b:type):[]int =
    for (D := dup[P], X : D.Items, Y := (D.C | 10) + 1) { Y }
Main()<transacts>:void =
    H := cell{}
    Y:pair(int, int) = dup(int){A := 7, B := 8, Items := array{5, 6}, C := 2}
    Z:pair(int, int) = pair(int, int){A := 1, B := 2}
    Print("Keep {Keep(Y).Length} {Keep(Z).Length}")
    R := Sum(H, array{Y, Z})
    Print("Sum {R.Length} {H.N}")
    C := Choose(Y)
    Print("Choose {C.Length}")
    for (V : C) { Print("{V}") }
    for (V : Nested(Y)) { Print("n{V}") }
