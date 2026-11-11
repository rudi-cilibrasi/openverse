# A continuation must retain the construction instance before its incoming inline alias disappears.
box(t:type) := struct { A:[]t = Concatenate(); B:int }
Dup(V:t where t:type):t = V | V
Inline(V:t where t:type):box(t) =
    A := (Dup(1) | Dup(2))
    B:box(t) = box{B := (Dup(1) | Dup(2))}
    B
Main():void =
    for (V := (Dup(1) | Dup("s")), B := Inline(V)):
        Print("{B.A.Length} {B.B}")
