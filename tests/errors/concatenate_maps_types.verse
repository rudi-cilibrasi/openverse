# expect: ConcatenateMaps takes maps of one type, not [int]int and [int]string
Main():void =
    X := ConcatenateMaps(map{1 => 1}, map{1 => "a"})
