# A for's generator after a refining cast whose source uses the cast's name
# (#243): the source casts the object again, typed under the refinement,
# as the body does when it uses the cast's name or the names those
# generators bind; the cast's clause first fails for an element of another
# class, undoing that element's clauses.
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    Items:[]t = array{}
Each(P:pair(a, b) where a:type, b:type):[]b =
    for (D := dup[P], Y : D.Items) { Y }
Each2(Ps:[]pair(a, b) where a:type, b:type):[]b =
    for (P : Ps, Print("p"), D := dup[P], N := D.Items.Length, Y : D.Items, Z : array{1, 2}):
        Print("{N} {Z}")
        D.A
Main():void =
    Y:pair(int, int) = dup(int){A := 1, B := 2, Items := array{5, 6}}
    Z:pair(int, int) = pair(int, int){A := 1, B := 2}
    Print("Each {Each(Y).Length} {Each(Z).Length}")
    Print("Each2 {Each2(array{Y, Z, Y}).Length}")
