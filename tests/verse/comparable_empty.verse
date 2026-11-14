# An empty array{} or map{} where a comparable is expected says nothing of
# its elements: it is the empty value, its own box, equal to every empty
# value (Book of Verse tests, Array.versetest:88, array{} = array{}).
AsComparable(X:comparable)<computes>:comparable = X
Main():void =
    X:comparable = array{}
    Y:comparable = array{}
    M:comparable = map{}
    if (X = Y) then Print("arrays equal")
    if (X = M, M = "") then Print("empty values equal")
    if (AsComparable(array{}) = AsComparable(array{})) then Print("through a function")
    if (X <> AsComparable(array{1})) then Print("not a full array")
    Cs:[]comparable = array{array{}, map{}, 1}
    if (Cs[0] = Cs[1], Cs[1] <> Cs[2]) then Print("elements")
