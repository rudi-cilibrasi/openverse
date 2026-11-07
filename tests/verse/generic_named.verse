# named parameters in generic functions (#119): inferred from every argument, defaults at the inferred types
F(X:t, ?Scale:int = 2 where t:type):tuple(t, int) = (X, Scale)
Wrap(X:t, ?Times:int = 1, ?Sep:string = "," where t:type):[]t =
    for (I := 1..Times) { X }
Pick(A:t, ?Other:t = A where t:type):t = Other
Fill(N:int, ?With:t where t:type):[]t = for (I := 1..N) { With }
Len(?Items:[]t = array{} where t:type):int = Items.Length
Main():void =
    P := F("a", ?Scale := 3)
    Q := F(7)
    Print("{P(0)} {P(1)} {Q(0)} {Q(1)}")
    W := Wrap(5, ?Sep := ";", ?Times := 3)
    Print("{W.Length}")
    Print(Pick("x"))
    Print(Pick("x", ?Other := "y"))
    Print("{Fill(2, ?With := 9).Length}")
    Print("{Len(?Items := array{1, 2, 3})}")
