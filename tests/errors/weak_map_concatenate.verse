# expect: ConcatenateMaps takes maps, and a weak_map is not one
# Book of Verse ch. 3: "you cannot use `ConcatenateMaps`"
Main():void =
    W:weak_map(int, int) = map{1 => 2}
    M := ConcatenateMaps(map{3 => 4}, W)
