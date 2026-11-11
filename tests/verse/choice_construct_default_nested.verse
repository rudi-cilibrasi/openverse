# Contextual field probes keep nested inline templates and their generic constructor instances.
box(t:type) := struct { A:[]t = Concatenate(); B:int }
outer(t:type) := struct { P:box(t); D:[]t = Concatenate(); C:int }
Inline(V:t where t:type):box(t) =
    B:box(t) = box{B := 1 | 2}
    B
Main():void =
    for (O:outer(int) := outer{P := Inline(1), C := 3 | 4}):
        Print("{O.P.A.Length} {O.P.B} {O.D.Length} {O.C}")
