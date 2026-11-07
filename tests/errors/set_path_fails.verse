# expect: this expression can fail, but it is not in a failure context
Main():void =
    var Grid:[][]int = array{array{0}}
    set Grid[0][0] = 1
