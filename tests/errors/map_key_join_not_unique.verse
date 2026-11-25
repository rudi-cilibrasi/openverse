# expect: expected ca, found cb
# Keys of two <unique> classes whose common class is not <unique>, so not
# comparable, do not join (#724, tests/verse/map_key_join).
base := class{}
ca := class<unique>(base){}
cb := class<unique>(base){}
Main():void =
    M := map{ca{} => "a", cb{} => "b"}
    Print("{M.Length}")
