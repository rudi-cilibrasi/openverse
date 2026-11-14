# A map literal whose values have nothing in common, with no value type
# expected, joins them at comparable or any, as an array literal's elements
# do (the Book's tests: "the result of a map literal with values of
# disjoint types is coerced to [key_type]any", Any.versetest 131-134,
# Map.versetest 160-164).
c := class{}
Strings():[string]any =
    M := map{"0" => 0, "0.0" => 0.0}
    M
Main():void =
    M := map{0 => "0", 1 => 1.0}
    N := map{0 => "0", 1 => 1.0, 2 => array{0, 1, 2}}
    O := map{0 => c{}, 1 => 1}
    Print("{M.Length} {N.Length} {Strings().Length} {O.Length}")
    if (M[0] = "0", N[2] = array{0, 1, 2}, not M[1] = 1) then Print("by value")
