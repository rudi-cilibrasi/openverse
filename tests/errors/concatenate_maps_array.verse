# expect: ConcatenateMaps takes maps, not []int
Main():void =
    X := ConcatenateMaps(map{1 => 2}, array{1})
