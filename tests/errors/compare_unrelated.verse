# expect: 3:8: '=' compares values of different types, []int and []string
Main():void =
    if (array{1} = array{"a"}) then Print("x")
