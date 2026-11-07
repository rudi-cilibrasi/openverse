Main():void =
    A := for (X := 1..160000) { 0 }
    if (B := A.Slice[0, 80000]) { Print("{B.Length}") }
