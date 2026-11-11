# A constructor with implicit arguments keeps each copied generic instance through shared helpers.
box(t:type) := struct { A:[]t = Concatenate(); B:int }
Dup(V:t where t:type):t = V | V
Inline(V:t where t:type):box(t) =
    B:box(t) = box{B := (Dup(1) | Dup(2))}
    B
Main():void =
    for (V := (Dup(1) | Dup("s")), A := (Dup(1) | Dup(2)), B := Inline(V), D := (Dup(1) | Dup(2)), A = 1, D = 1):
        Print("{B.A.Length} {B.B}")
