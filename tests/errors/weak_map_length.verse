# expect: a weak_map has no Length
# Book of Verse ch. 3: "There is no `Length` property" (weak_map.versetest:125, 3506)
Main():void =
    W:weak_map(int, int) = map{1 => 2}
    Print("{W.Length}")
