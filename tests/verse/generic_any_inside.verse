# An any inside a generic function's parameter type takes any type and
# binds nothing (#724): every value is an any, so an [int]string is a [t]any
# at t := int (the Book's tests, Any.versetest:60; Epic's compiler and Verse
# VM, UEFN 43.12, followup-refused/map-any-value-generic: count 2). The type
# parameters are inferred from the rest of the pattern.
MapCount(M:[t]any where t:subtype(comparable)):int = M.Length
First(M:[]tuple(t, any), D:t where t:type):t = if (P := M[0]) then P(0) else D
Opt(X:?any, Y:t where t:type):t = Y
Keys(M:[t]any where t:subtype(comparable))<transacts>:[]t = for (K -> V : M) { K }
c := class{ N:int = 3 }

Main():void =
    M:[int]string = map{0 => "0", 1 => "1"}
    Print("count {MapCount(M)}")
    Print("{MapCount(map{"a" => c{}})} {MapCount(map{1 => 1.5, 2 => 2.5})}")
    Print("{First(array{(1, "a"), (2, "b")}, 0)} {First(array{("x", 1.5)}, "d")}")
    Print("{Opt(option{1}, 5)} {Opt(false, 6)}")
    for (K : Keys(M)). Print("{K}")
    for (K : Keys(map{"k" => c{}})). Print(K)
