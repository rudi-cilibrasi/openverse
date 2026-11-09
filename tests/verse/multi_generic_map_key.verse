# a comparable type parameter as a map's key in an inlined generic call (#235, review of #282)
Keys(M:[t]int, X:t, Y:t where t:subtype(comparable))<decides>:t = (M[X]; X) | Y
Main():void =
    for (K := Keys[map{1 => 10}, 1, 2]) { Print("{K}") }
    if (K := Keys[map{"a" => 1}, "b", "c"]) then Print(K)
