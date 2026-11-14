# expect: set through a map's key can fail
Main():void =
    var W:weak_map(int, int) = map{}
    set W[1] = 2
