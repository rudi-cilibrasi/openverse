# expect: 3:8: '=' compares values of different types, []int and []float
Main():void =
    if (array{1} = array{1.0}) then Print("x")
