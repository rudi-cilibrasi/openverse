# ConcatenateMaps of maps keyed by different types (#724): "Concatenating
# two maps should result in a map with a key type and value type that are
# joins of the input key types and value types" (the Book's tests,
# ConcatenateMaps.versetest 44, 67). Classes join at the <unique> class
# above them, types with nothing else in common at comparable (Epic's
# compiler and Verse VM, UEFN 43.12,
# followup-refused/concatenate-maps-key-join: length 2). A key is then looked
# up as a comparable: the int 0 and the string "0" are two keys.
super_class := class<unique>{}
sub_class := class<unique>(super_class){}
other_sub := class(super_class){}

Main():void =
    Super := super_class{}
    Sub := sub_class{}
    Other := other_sub{}
    V0 := ConcatenateMaps(map{Sub => 0}, map{Super => 1})
    if (V0[Sub] = 0, V0[Super] = 1). Print("v0 {V0.Length}")
    V1 := ConcatenateMaps(map{Sub => 0}, map{Other => 1, Sub => 2})
    if (V1[Sub] = 2, V1[Other] = 1). Print("v1 {V1.Length}")
    V3 := ConcatenateMaps(map{0 => "0"}, map{"0" => "zero"})
    Print("v3 {V3.Length}")
    if (X := V3[0]). Print(X)
    if (X := V3["0"]). Print(X)
    if (not V3["1"], not V3[1], not V3[0.0]). Print("no other key")
    for (K -> V : V3). Print("pair {V}")
    # the values' types joined too
    V2 := ConcatenateMaps(map{"0" => 0}, map{"0.0" => 0.0})
    Print("v2 {V2.Length}")
    V4 := ConcatenateMaps(map{Sub => "a"}, map{Other => 2})
    Print("v4 {V4.Length}")
    # a map keyed by comparable and one keyed by int: the later value of a
    # key both have, at the later map's place
    V5 := ConcatenateMaps(V3, map{0 => "new", 1.5 => "f"})
    Print("v5 {V5.Length}")
    if (X := V5[0]). Print(X)
    for (K -> V : V5). Print("pair {V}")
    # maps from variables
    Ints:[int]string = map{1 => "one"}
    Strs:[string]string = map{"1" => "uno"}
    V6 := ConcatenateMaps(Ints, Strs)
    if (X := V6[1], Y := V6["1"]). Print("v6 {X} {Y}")
