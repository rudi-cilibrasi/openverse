# expect: ConcatenateMaps takes maps of one type
# Maps keyed by int and by rational are not joined (#724,
# tests/verse/concatenate_maps_key_join): give the key type.
Half()<transacts><decides>:rational = 1 / 2
Main():void =
    if (H := Half[]):
        M := ConcatenateMaps(map{1 => "a"}, map{H => "b"})
        Print("{M.Length}")
