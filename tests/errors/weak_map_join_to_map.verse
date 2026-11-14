# expect: expected [int]int, found weak_map(int, int): a weak_map is no map
# the join of a weak map and a map is a weak map (weak_map.versetest:104, 3510)
X:weak_map(int, int) = map{1 => 2, 3 => 4}
F():[int]int = if (true?) then X else map{5 => 6}
Main():void = {}
