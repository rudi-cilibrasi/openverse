# expect: 8:19: a weak_map cannot be iterated
# A weak map has no iteration (Book of Verse ch. 3), in a first's generator
# as in a for's.
key := class<unique>:
    Id:int = 0
Main():void =
    var W:weak_map(key, int) = map{}
    if (X := first{V : W; V > 0; V}) then Print("{X}")
