# expect: expected base, found other
# Keys of two <unique> classes with no class above both do not join
# (#724, tests/verse/map_key_join).
base := class<unique>{}
other := class<unique>{}
Main():void =
    M := map{base{} => "a", other{} => "b"}
    Print("{M.Length}")
