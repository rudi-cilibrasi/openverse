# expect: weak_map(int, int) is a weak_map, which is not (Book of Verse ch. 3: "no coercion to `comparable`")
# weak_map.versetest:156, 3509
Main():void =
    W:weak_map(int, int) = map{1 => 2}
    C:comparable = W
