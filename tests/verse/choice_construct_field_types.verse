# A provided field bound before a choice retains its expected array type.
pt := struct { A:[]int; B:int }
Main():void =
    for (P := pt{A := Concatenate(), B := 1 | 2}):
        Print("{P.A.Length} {P.B}")
