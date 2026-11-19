# Ints beyond 64 bits in containers (#724): equal values are one key of a
# map however they are computed; an index beyond 64 bits is past every
# array, so it fails as any index out of range does; a range with a bound
# beyond 64 bits gives its ints one by one, across the 64-bit boundary; and
# arrays, tuples and options of them compare by value.
Next(N:int)<computes>:int = N + 1

Main():void =
    Top:int = 9223372036854775807
    Big := Next(Top)
    M:[int]string = map{Big => "two to the 63", Big * Big => "two to the 126", Top => "top"}
    if (S := M[Top + 1]) then Print("key {S}")
    if (S := M[(Top + 1) * (Top + 1)]) then Print("key {S}")
    if (S := M[BitShiftLeft[1, 126]]) then Print("key {S}")
    if (S := M[Big - 1]) then Print("key {S}")
    if (not M[Big + 1]) then Print("no key 2^63 + 1")
    var N:[int]int = map{}
    if (set N[Big] = 1, set N[Top + 1] = 2, V := N[Big]) then Print("one entry, {N.Length}, value {V}")
    A := array{10, 20, 30}
    if (not A[Big], not A[-Big]) then Print("index beyond 64 bits fails")
    var B:[]int = array{1, 2}
    if (not (set B[Big] = 3)) then Print("set at an index beyond 64 bits fails")
    for (I := Top - 1..Top + 2):
        if (I > Top) then Print("past the top: + {I - Top}") else Print("top - {Top - I}")
    for (I := -Big - 2..-Big + 1):
        if (I < -Big) then Print("below the bottom: - {-Big - I}") else Print("bottom + {I + Big}")
    if (array{Big, 1} = array{Top + 1, 1}, array{Big} <> array{Top}) then Print("arrays")
    if ((Big, 2) = (Top + 1, 2), option{Big} = option{Top + 1}) then Print("tuples, options")
    R := for (I := Big..Big + 2) { I - Big }
    Print("range length {R.Length}")
