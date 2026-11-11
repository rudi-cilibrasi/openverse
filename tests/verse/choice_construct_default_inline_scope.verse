box(t:type) := struct { E:[]t = Concatenate(); B:int }
Inline(V:t where t:type):box(t) =
    B:box(t) = first{P:box(t) = box{B := 1 | 2}; P}
    B | B
Main():void =
    for (A := Inline(1), B := Inline("s")):
        Print("{A.E.Length} {B.E.Length}")
