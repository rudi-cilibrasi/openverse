# expect: expected int, found string
# A map literal's key type is the join of its keys' types (#724,
# tests/verse/map_key_join), but keys with nothing in common but
# comparable are refused unless the key type is given, M:[comparable]string
# (the Book's tests have that form only, Map.versetest: "Disjoint
# comparable key types are allowed as they are comparable").
Main():void =
    M := map{0 => "a", "0" => "b"}
    Print("{M.Length}")
