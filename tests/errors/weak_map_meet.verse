# expect: expected [int]int, found weak_map(int, int)
# the meet of the parameters is the map (weak_map.versetest:117, 3509)
F(X:[int]int)<decides>:int = X[1]
G(X:weak_map(int, int))<decides>:int = X[1]
Main()<decides>:void =
    X:weak_map(int, int) = map{1 => 2, 3 => 4}
    (if (true?) then F else G)[X] = 1
