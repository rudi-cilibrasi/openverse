# expect: ConcatenateMaps takes maps of one type
# Maps keyed by two <unique> classes whose common class is not <unique>
# have no key type in common (#724, tests/verse/concatenate_maps_key_join).
base := class{}
ca := class<unique>(base){}
cb := class<unique>(base){}
Main():void =
    M := ConcatenateMaps(map{ca{} => "a"}, map{cb{} => "b"})
    Print("{M.Length}")
