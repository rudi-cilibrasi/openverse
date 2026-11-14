# expect: a weak_map cannot be iterated
# Book of Verse ch. 3: "no iteration" (weak_map.versetest:130, 3524)
Main():void =
    W:weak_map(int, int) = map{1 => 2}
    for (K -> V : W) { Print("{K} {V}") }
