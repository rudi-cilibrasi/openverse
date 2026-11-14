# expect: expected []int
Main():void =
    var A:[]int = array{1}
    set A += (2, "wrong")
