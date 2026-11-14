# expect: a map key cannot be or hold an array or a map: []int is one
# (a weak map's key is a map's, Book of Verse ch. 3: "A weak_map is a map
# that does not keep its keys alive", a supertype of [k]v)
Main():void =
    var W:weak_map([]int, int) = map{}
